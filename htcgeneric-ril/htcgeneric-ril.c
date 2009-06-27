/* //device/system/htcgeneric-ril/htcgeneric-ril.c
**
** Copyright 2006, The Android Open Source Project
**
** Licensed under the Apache License, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**     http://www.apache.org/licenses/LICENSE-2.0
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
*/

#include <telephony/ril.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <pthread.h>
#include <alloca.h>
#include "atchannel.h"
#include "at_tok.h"
#include "misc.h"
#include <getopt.h>
#include <sys/socket.h>
#include <cutils/sockets.h>
#include <termios.h>

#define LOG_NDEBUG 0
#define LOG_TAG "RIL"
#include <utils/Log.h>

#define MAX_AT_RESPONSE 0x1000

/* pathname returned from RIL_REQUEST_SETUP_DEFAULT_PDP */
#define PPP_TTY_PATH "ppp0"

#ifdef USE_TI_COMMANDS

// Enable a workaround
// 1) Make incoming call, do not answer
// 2) Hangup remote end
// Expected: call should disappear from CLCC line
// Actual: Call shows as "ACTIVE" before disappearing
#define WORKAROUND_ERRONEOUS_ANSWER 1

// Some varients of the TI stack do not support the +CGEV unsolicited
// response. However, they seem to send an unsolicited +CME ERROR: 150
#define WORKAROUND_FAKE_CGEV 1
#endif

static void onRequest (int request, void *data, size_t datalen, RIL_Token t);
static RIL_RadioState currentState();
static int onSupports (int requestCode);
static void onCancel (RIL_Token t);
static const char *getVersion();
static int isRadioOn();
static int getSIMStatus();
static void onPDPContextListChanged(void *param);

extern const char * requestToString(int request);

/*** Static Variables ***/
static const RIL_RadioFunctions s_callbacks = {
    RIL_VERSION,
    onRequest,
    currentState,
    onSupports,
    onCancel,
    getVersion
};

#ifdef RIL_SHLIB
static const struct RIL_Env *s_rilenv;

#define RIL_onRequestComplete(t, e, response, responselen) s_rilenv->OnRequestComplete(t,e, response, responselen)
#define RIL_onUnsolicitedResponse(a,b,c) s_rilenv->OnUnsolicitedResponse(a,b,c)
#define RIL_requestTimedCallback(a,b,c) s_rilenv->RequestTimedCallback(a,b,c)
#endif

static RIL_RadioState sState = RADIO_STATE_UNAVAILABLE;

static pthread_mutex_t s_state_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t s_state_cond = PTHREAD_COND_INITIALIZER;

static int s_port = -1;
static const char * s_device_path = NULL;
static int          s_device_socket = 0;

/* trigger change to this with s_state_cond */
static int s_closed = 0;

static int sFD;     /* file desc of AT channel */
static char sATBuffer[MAX_AT_RESPONSE+1];
static char *sATBufferCur = NULL;

static const struct timeval TIMEVAL_SIMPOLL = {1,0};
static const struct timeval TIMEVAL_CALLSTATEPOLL = {0,500000};
static const struct timeval TIMEVAL_0 = {0,0};

#ifdef WORKAROUND_ERRONEOUS_ANSWER
// Max number of times we'll try to repoll when we think
// we have a AT+CLCC race condition
#define REPOLL_CALLS_COUNT_MAX 4

// Line index that was incoming or waiting at last poll, or -1 for none
static int s_incomingOrWaitingLine = -1;
// Number of times we've asked for a repoll of AT+CLCC
static int s_repollCallsCount = 0;
// Should we expect a call to be answered in the next CLCC?
static int s_expectAnswer = 0;
#endif /* WORKAROUND_ERRONEOUS_ANSWER */

static void pollSIMState (void *param);
static void setRadioState(RIL_RadioState newState);

static int isgsm=0;
static int dataCall=0;
static char erisystem[50];
static char *callwaiting_num;

static void handle_cdma_ccwa (const char *s)
{
    int err;
    char *line, *tmp;

    line = tmp = strdup(s);
    err = at_tok_start(&tmp);
    if (err)
        return;
    err = at_tok_nextstr(&tmp, &callwaiting_num);
    if (err)
        return;
    callwaiting_num = strdup(callwaiting_num);
    free(line);
    LOGE("successfully set callwaiting_numn");
}

extern char** cdma_to_gsmpdu(const char *);
extern char* gsm_to_cdmapdu(const char *);
extern int hex2int(const char);

static int clccStateToRILState(int state, RIL_CallState *p_state)

{
    switch(state) {
        case 0: *p_state = RIL_CALL_ACTIVE;   return 0;
        case 1: *p_state = RIL_CALL_HOLDING;  return 0;
        case 2: *p_state = RIL_CALL_DIALING;  return 0;
        case 3: *p_state = RIL_CALL_ALERTING; return 0;
        case 4: *p_state = RIL_CALL_INCOMING; return 0;
        case 5: *p_state = RIL_CALL_WAITING;  return 0;
        default: return -1;
    }
}

// some phone functions are controlled by msm_proc_comm through /sys
void writesys(char *name, char *val) {
	FILE *fout;
	char filename[256];
	strcpy(filename,"/sys/class/vogue_hw/");
	strcat(filename,name);
	fout=fopen(filename,"w");
	if(!fout) return;
	fprintf(fout,val);
	fclose(fout);
}
/**
 * Note: directly modified line and has *p_call point directly into
 * modified line
 */
static int callFromCLCCLine(char *line, RIL_Call *p_call)
{
        //+CLCC: 1,0,2,0,0,\"+18005551212\",145
        //     index,isMT,state,mode,isMpty(,number,TOA)?

    int err;
    int state;
    int mode;

    err = at_tok_start(&line);
    if (err < 0) goto error;

    err = at_tok_nextint(&line, &(p_call->index));
    if (err < 0) goto error;

    err = at_tok_nextbool(&line, &(p_call->isMT));
    if (err < 0) goto error;

    err = at_tok_nextint(&line, &state);
    if (err < 0) goto error;

    err = clccStateToRILState(state, &(p_call->state));
    if (err < 0) goto error;

    err = at_tok_nextint(&line, &mode);
    if (err < 0) goto error;

    p_call->isVoice = (mode == 0);

    err = at_tok_nextbool(&line, &(p_call->isMpty));
    if (err < 0) goto error;

    if (at_tok_hasmore(&line)) {
        err = at_tok_nextstr(&line, &(p_call->number));

        /* tolerate null here */
        if (err < 0) return 0;

        // Some lame implementations return strings
        // like "NOT AVAILABLE" in the CLCC line
        if (p_call->number != NULL
            && 0 == strspn(p_call->number, "+0123456789")
        ) {
            p_call->number = NULL;
        }

        err = at_tok_nextint(&line, &p_call->toa);
        if (err < 0) goto error;
    }

    return 0;

error:
    LOGE("invalid CLCC line\n");
    return -1;
}


/** do post-AT+CFUN=1 initialization */
static void onRadioPowerOn()
{
#ifdef USE_TI_COMMANDS
    /*  Must be after CFUN=1 */
    /*  TI specific -- notifications for CPHS things such */
    /*  as CPHS message waiting indicator */

    at_send_command("AT%CPHS=1", NULL);

    /*  TI specific -- enable NITZ unsol notifs */
    at_send_command("AT%CTZV=1", NULL);
#endif

    pollSIMState(NULL);
}

/** do post- SIM ready initialization */
static void onSIMReady()
{
	if(isgsm) {
    at_send_command_singleline("AT+CSMS=1", "+CSMS:", NULL);
    /*
     * Always send SMS messages directly to the TE
     *
     * mode = 1 // discard when link is reserved (link should never be
     *             reserved)
     * mt = 2   // most messages routed to TE
     * bm = 2   // new cell BM's routed to TE
     * ds = 1   // Status reports routed to TE
     * bfr = 1  // flush buffer
     */
	  at_send_command("AT+CNMI=1,2,2,1,1", NULL);
	}
}

static void requestRadioPower(void *data, size_t datalen, RIL_Token t)
{
	int onOff;

	int err;
	ATResponse *p_response = NULL;

	assert (datalen >= sizeof(int *));
	onOff = ((int *)data)[0];
	char *radio_off_gsm="AT+CFUN=0";
	char *radio_off_cdma="AT+CFUN=66";
	char *radio_off;
	
	if(isgsm) radio_off=radio_off_gsm;
		else
			radio_off=radio_off_cdma;

	if (onOff == 0 && sState != RADIO_STATE_OFF) {
		err = at_send_command(radio_off, &p_response);
		if (err < 0 || p_response->success == 0) goto error;			 
		setRadioState(RADIO_STATE_OFF);
	} 
	else 
		if (onOff > 0 && sState == RADIO_STATE_OFF) {
			err = at_send_command("AT+CFUN=1", &p_response);
			if (err < 0|| p_response->success == 0) {
					// Some stacks return an error when there is no SIM,
					// but they really turn the RF portion on
					// So, if we get an error, let's check to see if it
					// turned on anyway
	
					if (isRadioOn() != 1) {
							goto error;
					}
			}
			setRadioState(RADIO_STATE_SIM_NOT_READY);
	}

	at_response_free(p_response);
	RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
	return;
error:
	at_response_free(p_response);
	RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
}

static void requestOrSendPDPContextList(RIL_Token *t);

static void onPDPContextListChanged(void *param)
{
    requestOrSendPDPContextList(NULL);
}

static void requestPDPContextList(void *data, size_t datalen, RIL_Token t)
{
    requestOrSendPDPContextList(&t);
}

static void requestOrSendPDPContextList(RIL_Token *t)
{
    ATResponse *p_response;
    ATLine *p_cur;
    RIL_PDP_Context_Response *responses;
    int err;
    int n = 0;
    char *out;

  if (isgsm) {
    err = at_send_command_multiline ("AT+CGACT?", "+CGACT:", &p_response);
    if (err != 0 || p_response->success == 0) {
        if (t != NULL)
            RIL_onRequestComplete(*t, RIL_E_GENERIC_FAILURE, NULL, 0);
        else
            RIL_onUnsolicitedResponse(RIL_UNSOL_PDP_CONTEXT_LIST_CHANGED,
                                      NULL, 0);
        return;
    }

    for (p_cur = p_response->p_intermediates; p_cur != NULL;
         p_cur = p_cur->p_next)
        n++;

    responses = alloca(n * sizeof(RIL_PDP_Context_Response));

    int i;
    for (i = 0; i < n; i++) {
        responses[i].cid = -1;
        responses[i].active = -1;
        responses[i].type = "";
        responses[i].apn = "";
        responses[i].address = "";
    }

    RIL_PDP_Context_Response *response = responses;
    for (p_cur = p_response->p_intermediates; p_cur != NULL;
         p_cur = p_cur->p_next) {
        char *line = p_cur->line;

        err = at_tok_start(&line);
        if (err < 0)
            goto error;

        err = at_tok_nextint(&line, &response->cid);
        if (err < 0)
            goto error;

        err = at_tok_nextint(&line, &response->active);
        if (err < 0)
            goto error;

        response++;
    }

    at_response_free(p_response);

    err = at_send_command_multiline ("AT+CGDCONT?", "+CGDCONT:", &p_response);
    if (err != 0 || p_response->success == 0) {
        if (t != NULL)
            RIL_onRequestComplete(*t, RIL_E_GENERIC_FAILURE, NULL, 0);
        else
            RIL_onUnsolicitedResponse(RIL_UNSOL_PDP_CONTEXT_LIST_CHANGED,
                                      NULL, 0);
        return;
    }

    for (p_cur = p_response->p_intermediates; p_cur != NULL;
         p_cur = p_cur->p_next) {
        char *line = p_cur->line;
        int cid;
        char *type;
        char *apn;
        char *address;


        err = at_tok_start(&line);
        if (err < 0)
            goto error;

        err = at_tok_nextint(&line, &cid);
        if (err < 0)
            goto error;

        for (i = 0; i < n; i++) {
            if (responses[i].cid == cid)
                break;
        }

        if (i >= n) {
            /* details for a context we didn't hear about in the last request */
            continue;
        }

        err = at_tok_nextstr(&line, &out);
        if (err < 0)
            goto error;

        responses[i].type = alloca(strlen(out) + 1);
        strcpy(responses[i].type, out);

        err = at_tok_nextstr(&line, &out);
        if (err < 0)
            goto error;

        responses[i].apn = alloca(strlen(out) + 1);
        strcpy(responses[i].apn, out);

        err = at_tok_nextstr(&line, &out);
        if (err < 0)
            goto error;

        responses[i].address = alloca(strlen(out) + 1);
        strcpy(responses[i].address, out);
    }

    at_response_free(p_response);

  } else {
    //non-GSM
    n = 1;
    responses = alloca(sizeof(RIL_PDP_Context_Response));

    responses[0].cid = 1;
    responses[0].active = dataCall;
    responses[0].type = "";
    responses[0].apn = "internet";
    responses[0].address = "";
  }

    if (t != NULL)
        RIL_onRequestComplete(*t, RIL_E_SUCCESS, responses,
                              n * sizeof(RIL_PDP_Context_Response));
    else
        RIL_onUnsolicitedResponse(RIL_UNSOL_PDP_CONTEXT_LIST_CHANGED,
                                  responses,
                                  n * sizeof(RIL_PDP_Context_Response));

    return;

error:
    if (t != NULL)
        RIL_onRequestComplete(*t, RIL_E_GENERIC_FAILURE, NULL, 0);
    else
        RIL_onUnsolicitedResponse(RIL_UNSOL_PDP_CONTEXT_LIST_CHANGED,
                                  NULL, 0);

    at_response_free(p_response);
}

static void requestQueryNetworkSelectionMode(
                void *data, size_t datalen, RIL_Token t)
{
    int err;
    ATResponse *p_response = NULL;
    int response = 0;
    char *line;

  if(isgsm) { //this command conflicts with the network status command
    err = at_send_command_singleline("AT+COPS?", "+COPS:", &p_response);

    if (err < 0 || p_response->success == 0) {
        goto error;
    }

    line = p_response->p_intermediates->line;

    err = at_tok_start(&line);

    if (err < 0) {
        goto error;
    }

    err = at_tok_nextint(&line, &response);

    if (err < 0) {
        goto error;
    }
  }

    RIL_onRequestComplete(t, RIL_E_SUCCESS, &response, sizeof(int));
    at_response_free(p_response);
    return;
error:
    at_response_free(p_response);
    LOGE("requestQueryNetworkSelectionMode must never return error when radio is on");
    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
}

static void sendCallStateChanged(void *param)
{
    RIL_onUnsolicitedResponse (
        RIL_UNSOL_RESPONSE_CALL_STATE_CHANGED,
        NULL, 0);
}
int countValidCalls=0;
static void requestGetCurrentCalls(void *data, size_t datalen, RIL_Token t)
{
    int err;
    ATResponse *p_response;
    ATLine *p_cur;
    int countCalls;
    RIL_Call *p_calls;
    RIL_Call **pp_calls;
    int i;
    int needRepoll = 0;
    char *l_callwaiting_num=NULL;

#ifdef WORKAROUND_ERRONEOUS_ANSWER
    int prevIncomingOrWaitingLine;

    prevIncomingOrWaitingLine = s_incomingOrWaitingLine;
    s_incomingOrWaitingLine = -1;
#endif /*WORKAROUND_ERRONEOUS_ANSWER*/

    err = at_send_command_multiline ("AT+CLCC", "+CLCC:", &p_response);

    if (err != 0 || p_response->success == 0) {
        RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
        return;
    }

    /* count the calls */
    for (countCalls = 0, p_cur = p_response->p_intermediates
            ; p_cur != NULL
            ; p_cur = p_cur->p_next
    ) {
        countCalls++;
    }

    if (callwaiting_num) {
        /* This is not thread-safe.  Boo. */
        l_callwaiting_num = callwaiting_num;
        callwaiting_num = NULL;
        countCalls++;
    }

    /* yes, there's an array of pointers and then an array of structures */

    pp_calls = (RIL_Call **)alloca(countCalls * sizeof(RIL_Call *));
    p_calls = (RIL_Call *)alloca(countCalls * sizeof(RIL_Call));
    memset (p_calls, 0, countCalls * sizeof(RIL_Call));

    /* init the pointer array */
    for(i = 0; i < countCalls ; i++) {
        pp_calls[i] = &(p_calls[i]);
    }

    for (countValidCalls = 0, p_cur = p_response->p_intermediates
            ; p_cur != NULL
            ; p_cur = p_cur->p_next
    ) {
        err = callFromCLCCLine(p_cur->line, p_calls + countValidCalls);

        if (err != 0) {
            continue;
        }

#ifdef WORKAROUND_ERRONEOUS_ANSWER
        if (p_calls[countValidCalls].state == RIL_CALL_INCOMING
            || p_calls[countValidCalls].state == RIL_CALL_WAITING
        ) {
            s_incomingOrWaitingLine = p_calls[countValidCalls].index;
        }
#endif /*WORKAROUND_ERRONEOUS_ANSWER*/

        if (p_calls[countValidCalls].state != RIL_CALL_ACTIVE
            && p_calls[countValidCalls].state != RIL_CALL_HOLDING
        ) {
            needRepoll = 1;
        }
		if(p_calls[countValidCalls].isVoice) // only count voice calls
	        countValidCalls++;
    }

    if (l_callwaiting_num) {
        char fake_clcc[64];
        int index = p_calls[countValidCalls-1].index+1;

        /* Try not to use an index greater than 9 */
        if (index > 9) {
            int i;

            for (i=countValidCalls-2; i >= 0; i++) {
                if (p_calls[i].index < 9) {
                    index = p_calls[i].index+1;
                    break;
                }
            }
        }

        snprintf(fake_clcc, 64, "+CLCC: %d,0,5,0,0,\"%s\",129",
                 index, l_callwaiting_num);
        free(l_callwaiting_num);
        err = callFromCLCCLine(fake_clcc, p_calls + countValidCalls);
        if (err == 0) {
            countValidCalls++;
        }
    }

#ifdef WORKAROUND_ERRONEOUS_ANSWER
    // Basically:
    // A call was incoming or waiting
    // Now it's marked as active
    // But we never answered it
    //
    // This is probably a bug, and the call will probably
    // disappear from the call list in the next poll
    if (prevIncomingOrWaitingLine >= 0
            && s_incomingOrWaitingLine < 0
            && s_expectAnswer == 0
    ) {
        for (i = 0; i < countValidCalls ; i++) {

            if (p_calls[i].index == prevIncomingOrWaitingLine
                    && p_calls[i].state == RIL_CALL_ACTIVE
                    && s_repollCallsCount < REPOLL_CALLS_COUNT_MAX
            ) {
                LOGI(
                    "Hit WORKAROUND_ERRONOUS_ANSWER case."
                    " Repoll count: %d\n", s_repollCallsCount);
                s_repollCallsCount++;
                goto error;
            }
        }
    }

    s_expectAnswer = 0;
    s_repollCallsCount = 0;
#endif /*WORKAROUND_ERRONEOUS_ANSWER*/
	LOGI("Calls=%d,Valid=%d\n",countCalls,countValidCalls);
	if(countValidCalls==0) { // close audio if no voice calls.
		LOGI("Audio Close\n");
		writesys("audio","5");
	}
		
    RIL_onRequestComplete(t, RIL_E_SUCCESS, pp_calls,
            countValidCalls * sizeof (RIL_Call *));

    at_response_free(p_response);

#ifdef POLL_CALL_STATE
    if (countValidCalls) {  // We don't seem to get a "NO CARRIER" message from
                            // smd, so we're forced to poll until the call ends.
#else
    if (needRepoll) {
#endif
        RIL_requestTimedCallback (sendCallStateChanged, NULL, &TIMEVAL_CALLSTATEPOLL);
    }

    return;
error:
    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
    at_response_free(p_response);
}

static void requestDial(void *data, size_t datalen, RIL_Token t)
{
    RIL_Dial *p_dial;
    char *cmd;
    const char *clir;
    int ret;

    p_dial = (RIL_Dial *)data;

    switch (p_dial->clir) {
        case 1: clir = "I"; break;  /*invocation*/
        case 2: clir = "i"; break;  /*suppression*/
        default:
        case 0: clir = ""; break;   /*subscription default*/
    }
	writesys("audio","2");
    asprintf(&cmd, "ATD%s%s;", p_dial->address, clir);

    ret = at_send_command(cmd, NULL);

    free(cmd);

    /* success or failure is ignored by the upper layer here.
       it will call GET_CURRENT_CALLS and determine success that way */
    RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
}

static void requestWriteSmsToSim(void *data, size_t datalen, RIL_Token t)
{
    RIL_SMS_WriteArgs *p_args;
    char *cmd;
    int length;
    int err;
    ATResponse *p_response = NULL;

    p_args = (RIL_SMS_WriteArgs *)data;

    length = strlen(p_args->pdu)/2;
    asprintf(&cmd, "AT+CMGW=%d,%d", length, p_args->status);

    err = at_send_command_sms(cmd, p_args->pdu, "+CMGW:", &p_response);

    free(cmd);

    if (err != 0 || p_response->success == 0) goto error;

    RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
    at_response_free(p_response);

    return;
error:
    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
    at_response_free(p_response);
}

static void requestHangup(void *data, size_t datalen, RIL_Token t)
{
    int *p_line;

    int ret;
    char *cmd;

    p_line = (int *)data;

    // 3GPP 22.030 6.5.5
    // "Releases a specific active call X"
    asprintf(&cmd, "AT+CHLD=1%d", p_line[0]);

    ret = at_send_command(cmd, NULL);

    free(cmd);
//	writesys("audio","5");

    /* success or failure is ignored by the upper layer here.
       it will call GET_CURRENT_CALLS and determine success that way */
    RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
}

static void requestSignalStrength(void *data, size_t datalen, RIL_Token t)
{
    ATResponse *p_response = NULL;
    int err;
    int response[2];
    char *line;

	if(isgsm) 
		err = at_send_command_singleline("AT+CSQ", "+CSQ:", &p_response);
	else
    err = at_send_command_singleline("AT+HTC_CSQ", "+HTC_CSQ:", &p_response);

	if (err < 0 || p_response->success == 0) {
			RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
			goto error;
	}

	line = p_response->p_intermediates->line;
	
	err = at_tok_start(&line);
	if (err < 0) goto error;

	err = at_tok_nextint(&line, &(response[0]));
	if (err < 0) goto error;

	err = at_tok_nextint(&line, &(response[1]));
	if (err < 0) goto error;
	if(!isgsm) {
		response[0]*=2;
		response[1]=99;
	}

    RIL_onRequestComplete(t, RIL_E_SUCCESS, response, sizeof(response));

    at_response_free(p_response);
    return;

error:
    LOGE("requestSignalStrength must never return an error when radio is on");
    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
    at_response_free(p_response);
}

static void requestRegistrationState(int request, void *data,
                                        size_t datalen, RIL_Token t)
{
    int err;
    int response[4];
    char * responseStr[4];
    ATResponse *p_response = NULL;
    const char *cmd;
    const char *prefix;
    char *line, *p;
    int commas;
    int skip;
    int i;
    int count = 3;
	response[0]=1;
	response[1]=-1;
	response[2]=-1;

  if(isgsm) {
    if (request == RIL_REQUEST_REGISTRATION_STATE) {
        cmd = "AT+CREG?";
        prefix = "+CREG:";
    } else if (request == RIL_REQUEST_GPRS_REGISTRATION_STATE) {
        cmd = "AT+CGREG?";
        prefix = "+CGREG:";
    } else {
        assert(0);
        goto error;
    }
  } else {
    cmd = "AT+COPS?";
    prefix= "$HTC_SYSTYPE";
  }
    err = 1;
    for (i=0;i<4 && err != 0;i++)
	err = at_send_command_singleline(cmd, prefix, &p_response);

    if (err != 0) goto error;

    line = p_response->p_intermediates->line;

    err = at_tok_start(&line);
    if (err < 0) goto error;
  if (isgsm) {		
    /* Ok you have to be careful here
     * The solicited version of the CREG response is
     * +CREG: n, stat, [lac, cid]
     * and the unsolicited version is
     * +CREG: stat, [lac, cid]
     * The <n> parameter is basically "is unsolicited creg on?"
     * which it should always be
     *
     * Now we should normally get the solicited version here,
     * but the unsolicited version could have snuck in
     * so we have to handle both
     *
     * Also since the LAC and CID are only reported when registered,
     * we can have 1, 2, 3, or 4 arguments here
     *
     * finally, a +CGREG: answer may have a fifth value that corresponds
     * to the network type, as in;
     *
     *   +CGREG: n, stat [,lac, cid [,networkType]]
     */

    /* count number of commas */
	
    commas = 0;
    for (p = line ; *p != '\0' ;p++) {
        if (*p == ',') commas++;
    }

    switch (commas) {
        case 0: // +CREG: <stat> 
            err = at_tok_nextint(&line, &response[0]);
            if (err < 0) goto error;
            response[1] = -1;
            response[2] = -1;
        break;

        case 1: // +CREG: <n>, <stat> 
            err = at_tok_nextint(&line, &skip);
            if (err < 0) goto error;
            err = at_tok_nextint(&line, &response[0]);
            if (err < 0) goto error;
            response[1] = -1;
            response[2] = -1;
            if (err < 0) goto error;
        break;

	case 2: // +CREG: <stat>, <lac>, <cid> 
            err = at_tok_nextint(&line, &response[0]);
            if (err < 0) goto error;
            err = at_tok_nexthexint(&line, &response[1]);
            if (err < 0) goto error;
            err = at_tok_nexthexint(&line, &response[2]);
            if (err < 0) goto error;
        break;
        case 3: // +CREG: <n>, <stat>, <lac>, <cid> 
            err = at_tok_nextint(&line, &skip);
            if (err < 0) goto error;
            err = at_tok_nextint(&line, &response[0]);
            if (err < 0) goto error;
            err = at_tok_nexthexint(&line, &response[1]);
            if (err < 0) goto error;
            err = at_tok_nexthexint(&line, &response[2]);
            if (err < 0) goto error;

	    /* Hack for broken +CGREG responses which don't return the network type */
	    if(request == RIL_REQUEST_GPRS_REGISTRATION_STATE) {
		ATResponse *p_response_op = NULL;
    		err = at_send_command_singleline("AT+COPS?", "+COPS:", &p_response_op);
		/* We need to get the 4th return param */
		int commas_op;
		commas_op = 0;
		char *p_op, *line_op;					
		line_op = p_response_op->p_intermediates->line;
	
		for (p_op = line_op ; *p_op != '\0' ;p_op++) {
			if (*p_op == ',') commas_op++;
		}
					
		if (commas_op == 3) {
		    count = 4;
		    err = at_tok_start(&line_op);
		    err = at_tok_nextint(&line_op, &skip);
		    if (err < 0) goto error;
		    err = at_tok_nextint(&line_op, &skip);
		    if (err < 0) goto error;
		    err = at_tok_nextint(&line_op, &skip);
		    if (err < 0) goto error;
		    err = at_tok_nextint(&line_op, &response[3]);
		    if (err < 0) goto error;
		    /* Now translate to 'Broken Android Speak' - can't follow the GSM spec */						
		    switch(response[3]) {
			/* GSM/GSM Compact - aka GRPS */
			case 0: 
			case 1:
				response[3] = 1;
				break;
			/* EGPRS - aka EDGE */
			case 3:
				response[3] = 2;
				break;
			/* UTRAN - UMTS or better */
			case 2:
			case 4:
			case 5:
			case 6:
			case 7:
				response[3] = 3;
				break;
		    }
		}

		at_response_free(p_response_op);
    	    }
        break;
        // special case for CGREG, there is a fourth parameter
	// that is the network type (unknown/gprs/edge/umts)
	//
        case 4: // +CGREG: <n>, <stat>, <lac>, <cid>, <networkType> 
            err = at_tok_nextint(&line, &skip);
            if (err < 0) goto error;
            err = at_tok_nextint(&line, &response[0]);
            if (err < 0) goto error;
            err = at_tok_nexthexint(&line, &response[1]);
            if (err < 0) goto error;
            err = at_tok_nexthexint(&line, &response[2]);
            if (err < 0) goto error;
            err = at_tok_nexthexint(&line, &response[3]);
            if (err < 0) goto error;
            count = 4;
        break;
        default:
            goto error;
	}
  } else { //CDMA
    if (request == RIL_REQUEST_GPRS_REGISTRATION_STATE) {
	if ( dataCall == 0 )
	    response[0] = 3;
	else
	    response[0] = 1;
	err = at_tok_nextint(&line, &response[3]);
	if (response[3] < 1)
	    response[3] = 1;
	if (response[3] > 3)
	    response[3] = 3;
	count = 4;
    }
  }
    asprintf(&responseStr[0], "%d", response[0]);
    asprintf(&responseStr[1], "%d", response[1]);
    asprintf(&responseStr[2], "%d", response[2]);

    if (count > 3)
        asprintf(&responseStr[3], "%d", response[3]);

    RIL_onRequestComplete(t, RIL_E_SUCCESS, responseStr, count*sizeof(char*));
    at_response_free(p_response);

    return;
error:
    LOGE("requestRegistrationState must never return an error when radio is on");
    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
    at_response_free(p_response);
}

static void requestMute(void *data, size_t datalen, RIL_Token t)
{
	int err;
	ATResponse *p_response = NULL;
	int response[1];
	char *line;

	if(!isgsm) {
	    err = at_send_command_singleline("AT+CMUT?", "+CMUT:", &p_response);
	} else {
	    err = at_send_command_singleline("AT+MUT", "+CMUT:", &p_response);
	}
        if (err < 0 || p_response->success == 0) {
            goto error;
        } 
		
	line = p_response->p_intermediates->line;
	err = at_tok_start(&line);
        if (err < 0) goto error;
        err = at_tok_nextint(&line, &response[0]);

        RIL_onRequestComplete(t, RIL_E_SUCCESS, response, sizeof(char*));
        at_response_free(p_response);

	return;
error:
    LOGE("requestMute failed");
    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
    at_response_free(p_response);
}

static void requestOperator(void *data, size_t datalen, RIL_Token t)
{
    int err;
    int i;
    int skip;
    ATLine *p_cur;
    char *response[4];

    memset(response, 0, sizeof(response));

    ATResponse *p_response = NULL;
	if(isgsm) {
		err = at_send_command_multiline(
		    "AT+COPS=3,0;+COPS?;+COPS=3,1;+COPS?;+COPS=3,2;+COPS?",
		    "+COPS:", &p_response);

		/* we expect 3 lines here:
		 * +COPS: 0,0,"T - Mobile"
		 * +COPS: 0,1,"TMO"
		 * +COPS: 0,2,"310170"
		 */

		if (err != 0) goto error;

		for (i = 0, p_cur = p_response->p_intermediates
		        ; p_cur != NULL
		        ; p_cur = p_cur->p_next, i++
		) {
		    char *line = p_cur->line;

		    err = at_tok_start(&line);
		    if (err < 0) goto error;

		    err = at_tok_nextint(&line, &skip);
		    if (err < 0) goto error;

		    // If we're unregistered, we may just get
		    // a "+COPS: 0" response
		    if (!at_tok_hasmore(&line)) {
		        response[i] = NULL;
		        continue;
		    }

		    err = at_tok_nextint(&line, &skip);
		    if (err < 0) goto error;

		    // a "+COPS: 0, n" response is also possible
		    if (!at_tok_hasmore(&line)) {
		        response[i] = NULL;
		        continue;
		    }

		    err = at_tok_nextstr(&line, &(response[i]));
		    if (err < 0) goto error;
		}

		if (i < 3) {
		    goto error;
		}
		if (i == 3) {
			response[3] = '\0';
		}
	}
	else {
		response[0]=erisystem;
		response[1]="Android";
		response[2]="310995";
	}
    RIL_onRequestComplete(t, RIL_E_SUCCESS, response, sizeof(response));
    at_response_free(p_response);

    return;
error:
    LOGE("requestOperator must not return error when radio is on");
    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
    at_response_free(p_response);
}

static void requestSendSMS(void *data, size_t datalen, RIL_Token t)
{
    int err;
    const char *smsc;
    const char *pdu;
    int tpLayerLength;
    char *cmd1, *cmd2;
    RIL_SMS_Response response;
    ATResponse *p_response = NULL;
    char * cdma=0;
  	char sendstr[256];

    smsc = ((const char **)data)[0];
    pdu = ((const char **)data)[1];

	  tpLayerLength = strlen(pdu)/2;

    // "NULL for default SMSC"
    if (smsc == NULL) {
        smsc= "00";
    }
	if(!isgsm) {
	  strcpy(sendstr,"00");
		strcat(sendstr,pdu);
		LOGI("GSM PDU=%s",pdu);
    	cdma=gsm_to_cdmapdu(sendstr);
	  	tpLayerLength = strlen(cdma)/2;
	}
    asprintf(&cmd1, "AT+CMGS=%d", tpLayerLength);
	if(isgsm)
		asprintf(&cmd2, "%s%s", smsc, pdu);
	else
    asprintf(&cmd2, "%s", cdma);

    err = at_send_command_sms(cmd1, cmd2, "+CMGS:", &p_response);

    free(cmd1);
    free(cmd2);

    if (err != 0 || p_response->success == 0) goto error;

    memset(&response, 0, sizeof(response));

    /* FIXME fill in messageRef and ackPDU */

    RIL_onRequestComplete(t, RIL_E_SUCCESS, &response, sizeof(response));
    at_response_free(p_response);

    return;
error:
    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
    at_response_free(p_response);
}

static void requestSetupDefaultPDP(void *data, size_t datalen, RIL_Token t)
{
    const char *apn;
    char *cmd;
    int err;
    ATResponse *p_response = NULL;
    char *response[2] = { "1", PPP_TTY_PATH };

    apn = ((const char **)data)[0];

  if (isgsm) {
#ifdef USE_TI_COMMANDS
    // Config for multislot class 10 (probably default anyway eh?)
    err = at_send_command("AT%CPRIM=\"GMM\",\"CONFIG MULTISLOT_CLASS=<10>\"",
                        NULL);

    err = at_send_command("AT%DATA=2,\"UART\",1,,\"SER\",\"UART\",0", NULL);
#endif /* USE_TI_COMMANDS */

    int fd, qmistatus;
    size_t cur = 0;
    size_t len;
    ssize_t written, rlen;
    char status[32] = {0};
    int retry = 10;

    LOGD("requesting data connection to APN '%s'", apn);

    fd = open ("/dev/qmi", O_RDWR);
    if (fd >= 0) { /* the device doesn't exist on the emulator */

	    LOGD("opened the qmi device\n");
	    asprintf(&cmd, "up:%s", apn);
	    len = strlen(cmd);

	    while (cur < len) {
		    do {
	            written = write (fd, cmd + cur, len - cur);
	        } while (written < 0 && errno == EINTR);

	        if (written < 0) {
                LOGE("### ERROR writing to /dev/qmi");
                close(fd);
                goto error;
            }

            cur += written;
        }

        // wait for interface to come online

        do {
            sleep(1);
            do {
                rlen = read(fd, status, 31);
            } while (rlen < 0 && errno == EINTR);

            if (rlen < 0) {
                LOGE("### ERROR reading from /dev/qmi");
                close(fd);
                goto error;
            } else {
                status[rlen] = '\0';
                LOGD("### status: %s", status);
            }
        } while (strncmp(status, "STATE=up", 8) && strcmp(status, "online") && --retry);

        close(fd);

        if (retry == 0) {
            LOGE("### Failed to get data connection up\n");
	        goto error;
		}

        qmistatus = system("netcfg rmnet0 dhcp");

        LOGD("netcfg rmnet0 dhcp: status %d\n", qmistatus);

	    if (qmistatus < 0) goto error;

	} else {
		/*
        asprintf(&cmd, "AT+CGDCONT=1,\"IP\",\"%s\",,0,0", apn);
	    //FIXME check for error here
	    err = at_send_command(cmd, NULL);
	    free(cmd);

	    // Set required QoS params to default
	    err = at_send_command("AT+CGQREQ=1", NULL);

	    // Set minimum QoS params to default
	    err = at_send_command("AT+CGQMIN=1", NULL);

	    // packet-domain event reporting
	    err = at_send_command("AT+CGEREP=1,0", NULL);

	    // Hangup anything that's happening there now
	    err = at_send_command("AT+CGACT=1,0", NULL);

	    // Start data on PDP context 1
	    err = at_send_command("ATD*99***1#", &p_response);

	    if (err < 0 || p_response->success == 0) {
	        goto error;
	    }
			RIL_onRequestComplete(t, RIL_E_SUCCESS, response_k, sizeof(response_k));
			at_response_free(p_response);
			return;
//		err = at_send_command("ATH", NULL);
//		err = at_send_command("ATDT#777", NULL);
		*/
	}
  } else {
    // CDMA...
  }
  RIL_onRequestComplete(t, RIL_E_SUCCESS, response, sizeof(response));
	at_response_free(p_response);

	return;
error:
	RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
	at_response_free(p_response);

}

static void requestSMSAcknowledge(void *data, size_t datalen, RIL_Token t)
{
    int ackSuccess;
    int err;

    ackSuccess = ((int *)data)[0];

    if (ackSuccess == 1) {
        err = at_send_command("AT+CNMA=1", NULL);
    } else if (ackSuccess == 0)  {
        err = at_send_command("AT+CNMA=2", NULL);
    } else {
        LOGE("unsupported arg to RIL_REQUEST_SMS_ACKNOWLEDGE\n");
        goto error;
    }

    RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
error:
    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);

}

static void requestGetIMSI(void *data, size_t datalen, RIL_Token t)
{
    ATResponse *p_response = NULL;
    char *imsi;
    char *line;
    char *response;
    char *part;
    int err;
    if(isgsm) {
	err = at_send_command_numeric("AT+CIMI", &p_response);
        if (err < 0 || p_response->success == 0)
	    goto error;
        
	imsi = strdup(p_response->p_intermediates->line);
        
    } else {
        err = at_send_command_singleline("AT+COPS?", "+COPS:", &p_response);

        if (err < 0 || p_response->success == 0)
	    goto error;
        line = p_response->p_intermediates->line;

        at_tok_start(&line);
        err = at_tok_nextstr(&line, &response);
        if (err < 0)
	    goto error;
        err = at_tok_nextstr(&line, &response);
        if (err < 0)
	    goto error;
        err = at_tok_nextstr(&line, &response);
        if (err < 0)
	    goto error;

	part = strdup(response);

	at_response_free(p_response);

        err = at_send_command_singleline("AT+CNUM", "+CNUM:", &p_response);

        if (err < 0 || p_response->success == 0)
	    goto error;
        line = p_response->p_intermediates->line;

        at_tok_start(&line);
        err = at_tok_nextstr(&line, &response);
        if (err < 0)
	    goto error;
        err = at_tok_nextstr(&line, &response);
        if (err < 0)
	    goto error;
        //FIXME make it work with the real IMSI: asprintf(&imsi, "%s%s", part, response); //Real opID
        asprintf(&imsi, "310995000000000"); //Fake opID

	free (part);
    }

    RIL_onRequestComplete(t, RIL_E_SUCCESS, imsi, sizeof(char *));
    free (imsi);
    at_response_free(p_response);
    return;
error:
    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
    at_response_free(p_response);
}

static void  requestSIM_IO(void *data, size_t datalen, RIL_Token t)
{
    ATResponse *p_response = NULL;
    RIL_SIM_IO_Response sr;
    int err;
    char *cmd = NULL;
    RIL_SIM_IO *p_args;
    char *line;

    memset(&sr, 0, sizeof(sr));

    p_args = (RIL_SIM_IO *)data;

    /* FIXME handle pin2 */

    if (p_args->data == NULL) {
        asprintf(&cmd, "AT+CRSM=%d,%d,%d,%d,%d",
                    p_args->command, p_args->fileid,
                    p_args->p1, p_args->p2, p_args->p3);
    } else {
        asprintf(&cmd, "AT+CRSM=%d,%d,%d,%d,%d,%s",
                    p_args->command, p_args->fileid,
                    p_args->p1, p_args->p2, p_args->p3, p_args->data);
    }
  if(isgsm){
    err = at_send_command_singleline(cmd, "+CRSM:", &p_response);

    if (err < 0 || p_response->success == 0) {
        goto error;
    }

    line = p_response->p_intermediates->line;

    err = at_tok_start(&line);
    if (err < 0) goto error;

    err = at_tok_nextint(&line, &(sr.sw1));
    if (err < 0) goto error;

    err = at_tok_nextint(&line, &(sr.sw2));
    if (err < 0) goto error;

    if (at_tok_hasmore(&line)) {
        err = at_tok_nextstr(&line, &(sr.simResponse));
        if (err < 0) goto error;
    }
  } else {
	//CDMA
	if(p_args->fileid != 0x6f40) {
            LOGE("SIM IO Request: %s\n", cmd);
	    RIL_onRequestComplete(t, RIL_E_REQUEST_NOT_SUPPORTED, NULL, 0);
	    at_response_free(p_response);
	    free(cmd);
	    return;
	} else { //Asking for the MSISDN or phone number. 1+ bytes alpha id (leave null), 1 byte length of bcd number (set to 11), 1 byte TON/NPI (set to FF), 10 byte phone num, 1 byte capability id, 1 byte extension id
	    sr.sw1=144;
	    sr.sw2=0;

	    if(p_args->command == 192)
	    	asprintf(&sr.simResponse,"000000806f40040011a0aa01020120");
	    else {
		char * msid;
		char * response;
		int plus = 0;
		int length;
		int i;
		int curChar=0;

            	err = at_send_command_singleline("AT+CNUM", "+CNUM:", &p_response);

            	if (err < 0 || p_response->success == 0)
	            goto error;
            	line = p_response->p_intermediates->line;

            	at_tok_start(&line);
            	err = at_tok_nextstr(&line, &response);
            	if (err < 0)
	       	    goto error;
            	err = at_tok_nextstr(&line, &response);
            	if (err < 0)
	            goto error;

		if(response[0]=='+')
			plus = 1;

		length = strlen(response) - plus;
		asprintf(&msid,"%.2x%.2dFFFFFFFFFFFFFFFFFFFF",(length + 1) / 2 + 1, 81 + plus * 10);

		for (i = 0; curChar < length - 1; i+=2 ) {
			msid[5+i] = response[plus+curChar++];
	                msid[4+i] = response[plus+curChar++];
		}

		if ( length % 2) //One extra number
                	msid[4+length] = response[curChar];
		
	    	asprintf(&sr.simResponse,"ffffffffffffffffffffffffffffffffffff%sffff",msid);
		free(msid);
	    }
        }
  }
	
    RIL_onRequestComplete(t, RIL_E_SUCCESS, &sr, sizeof(sr));
    at_response_free(p_response);
    free(cmd);

    return;
error:
    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
    at_response_free(p_response);
    free(cmd);

}

static void  requestEnterSimPin(void*  data, size_t  datalen, RIL_Token  t)
{
    ATResponse   *p_response = NULL;
    int           err;
    char*         cmd = NULL;
    const char**  strings = (const char**)data;;

    if ( datalen == sizeof(char*) ) {
        asprintf(&cmd, "AT+CPIN=%s", strings[0]);
    } else if ( datalen == 2*sizeof(char*) ) {
        asprintf(&cmd, "AT+CPIN=%s,%s", strings[0], strings[1]);
    } else
        goto error;

    err = at_send_command_singleline(cmd, "+CPIN:", &p_response);
    free(cmd);

    if (err < 0 || p_response->success == 0) {
error:
        RIL_onRequestComplete(t, RIL_E_PASSWORD_INCORRECT, NULL, 0);
    } else {
        RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
    }
    at_response_free(p_response);
}


static void  requestSendUSSD(void *data, size_t datalen, RIL_Token t)
{
    const char *ussdRequest;

    ussdRequest = (char *)(data);


    RIL_onRequestComplete(t, RIL_E_REQUEST_NOT_SUPPORTED, NULL, 0);

// @@@ TODO

}


/*** Callback methods from the RIL library to us ***/

/**
 * Call from RIL to us to make a RIL_REQUEST
 *
 * Must be completed with a call to RIL_onRequestComplete()
 *
 * RIL_onRequestComplete() may be called from any thread, before or after
 * this function returns.
 *
 * Will always be called from the same thread, so returning here implies
 * that the radio is ready to process another command (whether or not
 * the previous command has completed).
 */
static void
onRequest (int request, void *data, size_t datalen, RIL_Token t)
{
    ATResponse *p_response;
    int err;

    LOGD("onRequest: %s", requestToString(request));

    /* Ignore all requests except RIL_REQUEST_GET_SIM_STATUS
     * when RADIO_STATE_UNAVAILABLE.
     */
    if (sState == RADIO_STATE_UNAVAILABLE
        && request != RIL_REQUEST_GET_SIM_STATUS
    ) {
        RIL_onRequestComplete(t, RIL_E_RADIO_NOT_AVAILABLE, NULL, 0);
        return;
    }

    /* Ignore all non-power requests when RADIO_STATE_OFF
     * (except RIL_REQUEST_GET_SIM_STATUS)
     */
    if (sState == RADIO_STATE_OFF
        && !(request == RIL_REQUEST_RADIO_POWER
            || request == RIL_REQUEST_GET_SIM_STATUS)
    ) {
        RIL_onRequestComplete(t, RIL_E_RADIO_NOT_AVAILABLE, NULL, 0);
        return;
    }

    switch (request) {
        case RIL_REQUEST_GET_SIM_STATUS: {
            int simStatus;

            simStatus = getSIMStatus();

            RIL_onRequestComplete(t, RIL_E_SUCCESS, &simStatus, sizeof(simStatus));
            break;
        }
        case RIL_REQUEST_GET_CURRENT_CALLS:
            requestGetCurrentCalls(data, datalen, t);
            break;
        case RIL_REQUEST_DIAL:
            requestDial(data, datalen, t);
            break;
        case RIL_REQUEST_HANGUP:
            requestHangup(data, datalen, t);
            break;
        case RIL_REQUEST_HANGUP_WAITING_OR_BACKGROUND:
            // 3GPP 22.030 6.5.5
            // "Releases all held calls or sets User Determined User Busy
            //  (UDUB) for a waiting call."
            if (isgsm)
                at_send_command("AT+CHLD=0", NULL);
            /* success or failure is ignored by the upper layer here.
               it will call GET_CURRENT_CALLS and determine success that way */
            RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
            break;
		case RIL_REQUEST_LAST_CALL_FAIL_CAUSE:
			//	writesys("audio","5");
				RIL_onRequestComplete(t,RIL_E_REQUEST_NOT_SUPPORTED, NULL, 0);
				break;
        case RIL_REQUEST_HANGUP_FOREGROUND_RESUME_BACKGROUND:
            // 3GPP 22.030 6.5.5
            // "Releases all active calls (if any exist) and accepts
            //  the other (held or waiting) call."
            at_send_command("AT+CHLD=1", NULL);
	    	// writesys("audio","5");

            /* success or failure is ignored by the upper layer here.
               it will call GET_CURRENT_CALLS and determine success that way */
            RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
            break;
        case RIL_REQUEST_SWITCH_WAITING_OR_HOLDING_AND_ACTIVE:
            // 3GPP 22.030 6.5.5
            // "Places all active calls (if any exist) on hold and accepts
            //  the other (held or waiting) call."
            if (isgsm)
                at_send_command("AT+CHLD=2", NULL);
            else
                at_send_command("AT+HTC_SENDFLASH", NULL);

#ifdef WORKAROUND_ERRONEOUS_ANSWER
            s_expectAnswer = 1;
#endif /* WORKAROUND_ERRONEOUS_ANSWER */

            /* success or failure is ignored by the upper layer here.
               it will call GET_CURRENT_CALLS and determine success that way */
            RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
            break;
        case RIL_REQUEST_ANSWER:
            at_send_command("ATA", NULL);
			writesys("audio","2");

#ifdef WORKAROUND_ERRONEOUS_ANSWER
            s_expectAnswer = 1;
#endif /* WORKAROUND_ERRONEOUS_ANSWER */

            /* success or failure is ignored by the upper layer here.
               it will call GET_CURRENT_CALLS and determine success that way */
            RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
            break;
        case RIL_REQUEST_CONFERENCE:
            // 3GPP 22.030 6.5.5
            // "Adds a held call to the conversation"
            at_send_command("AT+CHLD=3", NULL);

            /* success or failure is ignored by the upper layer here.
               it will call GET_CURRENT_CALLS and determine success that way */
            RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
            break;
        case RIL_REQUEST_UDUB:
            /* user determined user busy */
            /* sometimes used: ATH */
            at_send_command("ATH", NULL);

            /* success or failure is ignored by the upper layer here.
               it will call GET_CURRENT_CALLS and determine success that way */
            RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
            break;

        case RIL_REQUEST_SEPARATE_CONNECTION:
            {
                char  cmd[12];
                int   party = ((int*)data)[0];

                // Make sure that party is in a valid range.
                // (Note: The Telephony middle layer imposes a range of 1 to 7.
                // It's sufficient for us to just make sure it's single digit.)
                if (party > 0 && party < 10) {
                    sprintf(cmd, "AT+CHLD=2%d", party);
                    at_send_command(cmd, NULL);
                    RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
                } else {
                    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
                }
            }
            break;

        case RIL_REQUEST_SIGNAL_STRENGTH:
            requestSignalStrength(data, datalen, t);
            break;
        case RIL_REQUEST_REGISTRATION_STATE:
        case RIL_REQUEST_GPRS_REGISTRATION_STATE:
            requestRegistrationState(request, data, datalen, t);
            break;
        case RIL_REQUEST_OPERATOR:
            requestOperator(data, datalen, t);
            break;
        case RIL_REQUEST_RADIO_POWER:
            requestRadioPower(data, datalen, t);
            break;

	      case RIL_REQUEST_DTMF_STOP: 
	    			at_send_command("AT+CMUT=0", NULL);
	    			RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
	          break;
	    	case RIL_REQUEST_DTMF_START: 
	    //        case RIL_REQUEST_DTMF: 
				{
            char c = ((char *)data)[0];
            char *cmd;
						at_send_command("AT+CMUT=1", NULL);
            asprintf(&cmd, "AT+VTS=%c", (int)c);
            at_send_command(cmd, NULL);
						if(c=='*')
							 at_send_command("AT+WFSH", NULL);
            free(cmd);
            RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
            break;
        }
        case RIL_REQUEST_SEND_SMS:
            requestSendSMS(data, datalen, t);
            break;
        case RIL_REQUEST_SETUP_DEFAULT_PDP:
            requestSetupDefaultPDP(data, datalen, t);
            break;
        case RIL_REQUEST_SMS_ACKNOWLEDGE:
            requestSMSAcknowledge(data, datalen, t);
            break;

        case RIL_REQUEST_GET_IMSI:
            requestGetIMSI(data, datalen, t);
            break;

        case RIL_REQUEST_GET_IMEI:
            p_response = NULL;
		if(isgsm) {
			err = at_send_command_numeric("AT+CGSN", &p_response);
			if (err < 0 || p_response->success == 0) {
				RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
			} else {
				RIL_onRequestComplete(t, RIL_E_SUCCESS,
				p_response->p_intermediates->line, sizeof(char *));
			}
		} else {
			char * line;
			unsigned long int imei;
			char * imeiString;
			err = at_send_command_numeric("AT+GSN", &p_response);
			if (err < 0 || p_response->success == 0) {
				RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
			} else {
				line = p_response->p_intermediates->line;
				imei = (unsigned long)hex2int(line[9]) + (unsigned long)16*hex2int(line[8]) 
				    + (unsigned long)256*hex2int(line[7]) + (unsigned long)4096*hex2int(line[6]) 
				    + (unsigned long)65536*hex2int(line[5]) + (unsigned long)1048576*hex2int(line[4])
				    + (unsigned long)16777216*hex2int(line[3]) + (unsigned long)268435456*hex2int(line[2]);
				asprintf(&imeiString,"%015lu",imei);
				RIL_onRequestComplete(t, RIL_E_SUCCESS,imeiString, sizeof(char *));
				free(imeiString);
			}

		}
            at_response_free(p_response);
            break;
	    
        case RIL_REQUEST_SIM_IO:
								requestSIM_IO(data,datalen,t);
						break;
			
				case RIL_REQUEST_SEND_USSD:
						if(!isgsm) 
							RIL_onRequestComplete(t, RIL_E_REQUEST_NOT_SUPPORTED, NULL, 0);
						else    
							requestSendUSSD(data, datalen, t);
            break;

        case RIL_REQUEST_CANCEL_USSD:
            p_response = NULL;
            err = at_send_command_numeric("AT+CUSD=2", &p_response);

            if (err < 0 || p_response->success == 0) {
                RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
            } else {
                RIL_onRequestComplete(t, RIL_E_SUCCESS,
                    p_response->p_intermediates->line, sizeof(char *));
            }
            at_response_free(p_response);
	    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
            break;
	    

        case RIL_REQUEST_SET_NETWORK_SELECTION_AUTOMATIC:
	    				at_send_command("AT+COPS=0", NULL);
	    			RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
          	break;

        case RIL_REQUEST_PDP_CONTEXT_LIST:
            requestPDPContextList(data, datalen, t);
            break;

        case RIL_REQUEST_QUERY_NETWORK_SELECTION_MODE:
            requestQueryNetworkSelectionMode(data, datalen, t);
            break;

        case RIL_REQUEST_OEM_HOOK_RAW:
            // echo back data
            RIL_onRequestComplete(t, RIL_E_SUCCESS, data, datalen);
            break;

	    
        case RIL_REQUEST_OEM_HOOK_STRINGS: {
            int i;
            const char ** cur;

	        if(isgsm) {
            LOGD("got OEM_HOOK_STRINGS: 0x%8p %lu", data, (long)datalen);


            for (i = (datalen / sizeof (char *)), cur = (const char **)data ;
                    i > 0 ; cur++, i --) {
                LOGD("> '%s'", *cur);
            }

            // echo back strings
            RIL_onRequestComplete(t, RIL_E_SUCCESS, data, datalen);
	        }
	        else
		        RIL_onRequestComplete(t, RIL_E_REQUEST_NOT_SUPPORTED, NULL, 0);
          break;
        }

	    case RIL_REQUEST_WRITE_SMS_TO_SIM:
	    if(!isgsm) 
		    RIL_onRequestComplete(t, RIL_E_REQUEST_NOT_SUPPORTED, NULL, 0);
	    else {
	        requestWriteSmsToSim(data, datalen, t);
	    RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
	    }
	          break;
    case RIL_REQUEST_DELETE_SMS_ON_SIM: {
            char * cmd;
            p_response = NULL;
	        	    if(!isgsm) 
		    RIL_onRequestComplete(t, RIL_E_REQUEST_NOT_SUPPORTED, NULL, 0);
	    else {
            asprintf(&cmd, "AT+CMGD=%d", ((int *)data)[0]);
            err = at_send_command(cmd, &p_response);
            free(cmd);
            if (err < 0 || p_response->success == 0) {
                RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
            } else {
                RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
            }
            at_response_free(p_response);
        }
    }
	    break;

	case RIL_REQUEST_SET_MUTE: {
		char * cmd;
		p_response = NULL;
			if (((int *)data)[0])
	            asprintf(&cmd, "AT+CMUT=1");
			else
	            asprintf(&cmd, "AT+CMUT=0");				
            err = at_send_command(cmd, &p_response);
            free(cmd);
            if (err < 0 || p_response->success == 0) {
                RIL_onRequestComplete(t, RIL_E_GENERIC_FAILURE, NULL, 0);
            } else {
                RIL_onRequestComplete(t, RIL_E_SUCCESS, NULL, 0);
            }
            at_response_free(p_response);
	    }
	    break;
		
	case RIL_REQUEST_GET_MUTE: {
            requestMute(data, datalen, t);
	    }
	    break;
		

        case RIL_REQUEST_ENTER_SIM_PIN:
        case RIL_REQUEST_ENTER_SIM_PUK:
        case RIL_REQUEST_ENTER_SIM_PIN2:
        case RIL_REQUEST_ENTER_SIM_PUK2:
        case RIL_REQUEST_CHANGE_SIM_PIN:
        case RIL_REQUEST_CHANGE_SIM_PIN2:
	        if(isgsm)
	                  requestEnterSimPin(data, datalen, t);
	        else
		        RIL_onRequestComplete(t, RIL_E_REQUEST_NOT_SUPPORTED, NULL, 0);
            break;

        default:
            RIL_onRequestComplete(t, RIL_E_REQUEST_NOT_SUPPORTED, NULL, 0);
            break;
    }
}

/**
 * Synchronous call from the RIL to us to return current radio state.
 * RADIO_STATE_UNAVAILABLE should be the initial state.
 */
static RIL_RadioState
currentState()
{
    return sState;
}
/**
 * Call from RIL to us to find out whether a specific request code
 * is supported by this implementation.
 *
 * Return 1 for "supported" and 0 for "unsupported"
 */

static int
onSupports (int requestCode)
{
    //@@@ todo

    return 1;
}

static void onCancel (RIL_Token t)
{
    //@@@todo

}

static const char * getVersion(void)
{
    return "HTC Vogue Community RIL 0.8";
}

static void
setRadioState(RIL_RadioState newState)
{
    RIL_RadioState oldState;

    pthread_mutex_lock(&s_state_mutex);

    oldState = sState;

    if (s_closed > 0) {
        // If we're closed, the only reasonable state is
        // RADIO_STATE_UNAVAILABLE
        // This is here because things on the main thread
        // may attempt to change the radio state after the closed
        // event happened in another thread
        newState = RADIO_STATE_UNAVAILABLE;
    }

    if (sState != newState || s_closed > 0) {
        sState = newState;

        pthread_cond_broadcast (&s_state_cond);
    }

    pthread_mutex_unlock(&s_state_mutex);


    /* do these outside of the mutex */
    if (sState != oldState) {
        RIL_onUnsolicitedResponse (RIL_UNSOL_RESPONSE_RADIO_STATE_CHANGED,
                                    NULL, 0);

        /* FIXME onSimReady() and onRadioPowerOn() cannot be called
         * from the AT reader thread
         * Currently, this doesn't happen, but if that changes then these
         * will need to be dispatched on the request thread
         */
        if (sState == RADIO_STATE_SIM_READY) {
            onSIMReady();
        } else if (sState == RADIO_STATE_SIM_NOT_READY) {
            onRadioPowerOn();
        }
    }
}

/** returns one of RIM_SIM_*. Returns RIL_SIM_NOT_READY on error */
static int
getSIMStatus()
{
    ATResponse *p_response = NULL;
    int err;
    int ret;
    char *cpinLine;
    char *cpinResult;

    if (sState == RADIO_STATE_OFF || sState == RADIO_STATE_UNAVAILABLE) {
        ret = RIL_SIM_NOT_READY;
        goto done;
    }
	/*
    err = at_send_command_singleline("AT+CPIN?", "+CPIN:", &p_response);

    if (err != 0) {
        ret = RIL_SIM_NOT_READY;
        goto done;
    }

    switch (at_get_cme_error(p_response)) {
        case CME_SUCCESS:
            break;

        case CME_SIM_NOT_INSERTED:
            ret = RIL_SIM_ABSENT;
            goto done;

        default:
            ret = RIL_SIM_NOT_READY;
            goto done;
    }
*/
    /* CPIN? has succeeded, now look at the result */
	/*
    cpinLine = p_response->p_intermediates->line;
    err = at_tok_start (&cpinLine);

    if (err < 0) {
        ret = RIL_SIM_NOT_READY;
        goto done;
    }

    err = at_tok_nextstr(&cpinLine, &cpinResult);

    if (err < 0) {
        ret = RIL_SIM_NOT_READY;
        goto done;
    }

    if (0 == strcmp (cpinResult, "SIM PIN")) {
        ret = RIL_SIM_PIN;
        goto done;
    } else if (0 == strcmp (cpinResult, "SIM PUK")) {
        ret = RIL_SIM_PUK;
        goto done;
    } else if (0 == strcmp (cpinResult, "PH-NET PIN")) {
        return RIL_SIM_NETWORK_PERSONALIZATION;
    } else if (0 != strcmp (cpinResult, "READY"))  {
	*/
        /* we're treating unsupported lock types as "sim absent" */
	/*        ret = RIL_SIM_ABSENT;
        goto done;
    }

    at_response_free(p_response);
    p_response = NULL;
    cpinResult = NULL;
*/
    ret = RIL_SIM_READY;

done:
    at_response_free(p_response);
    return ret;
}


/**
 * SIM ready means any commands that access the SIM will work, including:
 *  AT+CPIN, AT+CSMS, AT+CNMI, AT+CRSM
 *  (all SMS-related commands)
 */

static void pollSIMState (void *param)
{
    ATResponse *p_response;
    int ret;

    if (sState != RADIO_STATE_SIM_NOT_READY) {
        // no longer valid to poll
        return;
    }
	if(!isgsm) {
		setRadioState(RADIO_STATE_SIM_READY);
		return;
	}
    switch(getSIMStatus()) {
        case RIL_SIM_ABSENT:
        case RIL_SIM_PIN:
        case RIL_SIM_PUK:
        case RIL_SIM_NETWORK_PERSONALIZATION:
        default:
            setRadioState(RADIO_STATE_SIM_LOCKED_OR_ABSENT);
        return;

        case RIL_SIM_NOT_READY:
            RIL_requestTimedCallback (pollSIMState, NULL, &TIMEVAL_SIMPOLL);
        return;

        case RIL_SIM_READY:
            setRadioState(RADIO_STATE_SIM_READY);
        return;
    }
}

/** returns 1 if on, 0 if off, and -1 on error */
static int isRadioOn()
{
    ATResponse *p_response = NULL;
    int err;
    char *line;
    char ret;

    err = at_send_command_singleline("AT+CFUN?", "+CFUN:", &p_response);

    if (err < 0 || p_response->success == 0) {
        // assume radio is off
        goto error;
    }

    line = p_response->p_intermediates->line;

    err = at_tok_start(&line);
    if (err < 0) goto error;

    err = at_tok_nextbool(&line, &ret);
    if (err < 0) goto error;

    at_response_free(p_response);

    return (int)ret;

error:

    at_response_free(p_response);
    return -1;
}

/**
 * Initialize everything that can be configured while we're still in
 * AT+CFUN=0
 */
static void initializeCallback(void *param)
{
    ATResponse *p_response = NULL;
    int err;

    setRadioState (RADIO_STATE_OFF);

    at_handshake();

    /* note: we don't check errors here. Everything important will
       be handled in onATTimeout and onATReaderClosed */

  if(!isgsm) {
	strcpy(erisystem,"Android");
    /*  atchannel is tolerant of echo but it must */
    /*  have verbose result codes */
        at_send_command("ATV1", NULL);
    /*  echo off */
        at_send_command("ATE0", NULL);
    /*  No auto-answer */
        at_send_command("ATS0=0", NULL);
    /*  send results */
        at_send_command("ATQ0", NULL);
    /*  check for busy, don't check for dialone */
        at_send_command("ATX3", NULL);
    /*  set DCD depending on service */
        at_send_command("AT&C1", NULL);
    /*  set DTR according to service */
        at_send_command("AT&D1", NULL);
    /*  Extended errors, detailed rings, unknown, modulate data, no mute */
        at_send_command("AT+CMEE=1;+CRC=1;+CR=1;+CMOD=0;+CMUT=0", NULL);
        at_send_command("AT", NULL);
    /*  bring up the device, also resets the stack */
        at_send_command("AT+CFUN=1", NULL);
    /*  Not muted */
        at_send_command("AT+CMUT=0", NULL);
    /*  caller id = yes */
        at_send_command("AT+CLIP=1", NULL);
    /*  don't hide outgoing callerID */
        at_send_command("AT+CLIR=0", NULL);
        at_send_command("AT", NULL);

        at_send_command("AT+COPS=0", NULL);
//      at_send_command("AT+HTC_GPSONE=4", NULL);
        at_send_command("AT+CLVL=102", NULL);
        at_send_command("AT+CLVL=51", NULL);

  } else {
    /*  atchannel is tolerant of echo but it must */
    /*  have verbose result codes */
    at_send_command("ATE0Q0V1", NULL);
	
    /*  No auto-answer */
    at_send_command("ATS0=0", NULL);

    /*  Extended errors */
    at_send_command("AT+CMEE=1", NULL);

    /*  Network registration events */
    err = at_send_command("AT+CREG=2", &p_response);

    /* some handsets -- in tethered mode -- don't support CREG=2 */
    if (err < 0 || p_response->success == 0) {
        at_send_command("AT+CREG=1", NULL);
    }

    at_response_free(p_response);

    at_send_command("AT+CGREG=?", NULL);
    /*  GPRS registration events */
    at_send_command("AT+CGREG=2", NULL);

    /*  Call Waiting notifications */
    at_send_command("AT+CCWA=1", NULL);

    /*  Alternating voice/data off */
    at_send_command("AT+CMOD=0", NULL);

    /*  Not muted */
    at_send_command("AT+CMUT=0", NULL);

    /*  +CSSU unsolicited supp service notifications */
    at_send_command("AT+CSSN=0,1", NULL);

    /*  no connected line identification */
    at_send_command("AT+COLP=0", NULL);

    /*  HEX character set */
    at_send_command("AT+CSCS=\"HEX\"", NULL);

    /*  USSD unsolicited */
    at_send_command("AT+CUSD=1", NULL);

    /*  Enable +CGEV GPRS event notifications, but don't buffer */
    at_send_command("AT+CGEREP=1,0", NULL);

    /*  SMS PDU mode */
    at_send_command("AT+CMGF=0", NULL);

#ifdef USE_TI_COMMANDS

    at_send_command("AT%CPI=3", NULL);

    /*  TI specific -- notifications when SMS is ready (currently ignored) */
    at_send_command("AT%CSTAT=1", NULL);

#endif /* USE_TI_COMMANDS */

  }
    /* assume radio is off on error */
    if (isRadioOn() > 0) {
        setRadioState (RADIO_STATE_SIM_NOT_READY);
    }
}

static void waitForClose()
{
    pthread_mutex_lock(&s_state_mutex);

    while (s_closed == 0) {
        pthread_cond_wait(&s_state_cond, &s_state_mutex);
    }

    pthread_mutex_unlock(&s_state_mutex);
}

/**
 * Called by atchannel when an unsolicited line appears
 * This is called on atchannel's reader thread. AT commands may
 * not be issued here
 */
static void onUnsolicited (const char *s, const char *sms_pdu)
{
    int err;

    /* Ignore unsolicited responses until we're initialized.
     * This is OK because the RIL library will poll for initial state
     */
    if (sState == RADIO_STATE_UNAVAILABLE) {
        return;
    }

    if (strStartsWith(s, "%CTZV:") || strStartsWith(s, "+HTCCTZV:")) {
        /* TI specific -- NITZ time */
        char *response;

        at_tok_start(&s);

        err = at_tok_nextstr(&s, &response);

        if (err != 0) {
            LOGE("invalid NITZ line %s\n", s);
        } else {
            RIL_onUnsolicitedResponse (
                RIL_UNSOL_NITZ_TIME_RECEIVED,
                response, strlen(response));
        }
    } else if (strStartsWith(s,"+CRING:")
                || strStartsWith(s,"RING")
                || strStartsWith(s,"NO CARRIER")
                || strStartsWith(s,"+CCWA")
    ) {
        if (strStartsWith(s,"+CCWA") && !isgsm) {
            /* Handle CCWA specially */
            handle_cdma_ccwa(s);
        }
        RIL_onUnsolicitedResponse (
            RIL_UNSOL_RESPONSE_CALL_STATE_CHANGED,
            NULL, 0);
#ifdef WORKAROUND_FAKE_CGEV
        RIL_requestTimedCallback (onPDPContextListChanged, NULL, NULL);
#endif /* WORKAROUND_FAKE_CGEV */
    } else if (strStartsWith(s,"+CREG:")
                || strStartsWith(s,"+CGREG:")
		|| strStartsWith(s,"$HTC_SYSTYPE:")
    ) {
        RIL_onUnsolicitedResponse (
            RIL_UNSOL_RESPONSE_NETWORK_STATE_CHANGED,
            NULL, 0);
#ifdef WORKAROUND_FAKE_CGEV
        RIL_requestTimedCallback (onPDPContextListChanged, NULL, NULL);
#endif /* WORKAROUND_FAKE_CGEV */
    } else if (strStartsWith(s, "+CMT:")) {
	    if(!isgsm) {
				char **pdu;
				pdu=cdma_to_gsmpdu(sms_pdu);
				while(*pdu) {
					//				dbg(3,"RIL","SMS GSM_PDU=%s\n",*pdu); 
					RIL_onUnsolicitedResponse (
							RIL_UNSOL_RESPONSE_NEW_SMS,*pdu,strlen(*pdu));
					pdu++;
				}
	    } else
		    RIL_onUnsolicitedResponse (
            RIL_UNSOL_RESPONSE_NEW_SMS,
            sms_pdu, strlen(sms_pdu));


    } else if (strStartsWith(s, "+CDS:")) {
        RIL_onUnsolicitedResponse (
            RIL_UNSOL_RESPONSE_NEW_SMS_STATUS_REPORT,
            sms_pdu, strlen(sms_pdu));
    } else if (strStartsWith(s, "+CGEV:")) {
        /* Really, we can ignore NW CLASS and ME CLASS events here,
         * but right now we don't since extranous
         * RIL_UNSOL_PDP_CONTEXT_LIST_CHANGED calls are tolerated
         */
        /* can't issue AT commands here -- call on main thread */
        RIL_requestTimedCallback (onPDPContextListChanged, NULL, NULL);
#ifdef WORKAROUND_FAKE_CGEV
    } else if (strStartsWith(s, "+CME ERROR: 150")) {
        RIL_requestTimedCallback (onPDPContextListChanged, NULL, NULL);
#endif /* WORKAROUND_FAKE_CGEV */
    } else if (strStartsWith(s, "$HTC_3GIND:")) {
	//set the 3G indicator...
		
	int ind3g = -1;

        at_tok_start(&s);

        err = at_tok_nextint(&s, &ind3g);

        if (err != 0) {
            LOGE("invalid 3GIND %s\n", s);
        } else {
	    if ( ind3g > -1 && ind3g < 3 ) {
		if ( (dataCall == 1 && ind3g == 0) || (dataCall == 0 && ind3g != 0) ){
    		    if ( dataCall == 0 )
			dataCall = 1;
    		    else
			dataCall = 0;
		    sleep(5);
        	    RIL_requestTimedCallback (onPDPContextListChanged, NULL, NULL);
		    RIL_onUnsolicitedResponse (
		        RIL_UNSOL_RESPONSE_NETWORK_STATE_CHANGED,
        		NULL, 0);
		}
	    }
        }
    } else if (strStartsWith(s, "$HTC_ERIIND:")) {
	int temp;
	char *newEri;
	at_tok_start(&s);

	at_tok_nextint(&s, &temp);
	at_tok_nextint(&s, &temp);
	at_tok_nextint(&s, &temp);
	at_tok_nextint(&s, &temp);
	at_tok_nextint(&s, &temp);
	at_tok_nextint(&s, &temp);
	at_tok_nextint(&s, &temp);
	at_tok_nextstr(&s, &newEri);
	if(strlen(newEri)<50)
	    strcpy(erisystem,newEri);
    }
}

/* Called on command or reader thread */
static void onATReaderClosed()
{
    LOGI("AT channel closed\n");
    at_close();
    s_closed = 1;

    setRadioState (RADIO_STATE_UNAVAILABLE);
}

/* Called on command thread */
static void onATTimeout()
{
    LOGI("AT channel timeout; closing\n");
    at_close();

    s_closed = 1;

    /* FIXME cause a radio reset here */

    setRadioState (RADIO_STATE_UNAVAILABLE);
}

static void usage(char *s)
{
#ifdef RIL_SHLIB
    fprintf(stderr, "htcgeneric-ril requires: -p <tcp port> or -d /dev/tty_device\n");
#else
    fprintf(stderr, "usage: %s [-p <tcp port>] [-d /dev/tty_device]\n", s);
    exit(-1);
#endif
}

static void *
mainLoop(void *param)
{
    int fd;
    int ret;

    AT_DUMP("== ", "entering mainLoop()", -1 );
    at_set_on_reader_closed(onATReaderClosed);
    at_set_on_timeout(onATTimeout);

    for (;;) {
        fd = -1;
        while  (fd < 0) {
            if (s_port > 0) {
                fd = socket_loopback_client(s_port, SOCK_STREAM);
            } else if (s_device_socket) {
                fd = socket_local_client( s_device_path,
                                          ANDROID_SOCKET_NAMESPACE_FILESYSTEM,
                                          SOCK_STREAM );
            } else if (s_device_path != NULL) {
                fd = open (s_device_path, O_RDWR);
                if ( fd >= 0 && !memcmp( s_device_path, "/dev/ttyS", 9 ) ) {
                    /* disable echo on serial ports */
                    struct termios  ios;
                    tcgetattr( fd, &ios );
                    ios.c_lflag = 0;  /* disable ECHO, ICANON, etc... */
                    tcsetattr( fd, TCSANOW, &ios );
                }
            }

            if (fd < 0) {
                perror ("opening AT interface. retrying...");
                sleep(10);
                /* never returns */
            }
        }

        s_closed = 0;
        ret = at_open(fd, onUnsolicited);

        if (ret < 0) {
            LOGE ("AT error %d on at_open\n", ret);
            return 0;
        }

        RIL_requestTimedCallback(initializeCallback, NULL, &TIMEVAL_0);

        // Give initializeCallback a chance to dispatched, since
        // we don't presently have a cancellation mechanism
        sleep(1);

        waitForClose();
        LOGI("Re-opening after close");
    }
}

#ifdef RIL_SHLIB

pthread_t s_tid_mainloop;

const RIL_RadioFunctions *RIL_Init(const struct RIL_Env *env, int argc, char **argv)
{
    int ret;
    int fd = -1;
    int opt;
    pthread_attr_t attr;

    s_rilenv = env;
	
		if(open("/sys/class/vogue_hw/gsmphone",O_RDONLY)>0)
			isgsm=1;
		else 
			isgsm=0;

    while ( -1 != (opt = getopt(argc, argv, "p:d:s:"))) {
        switch (opt) {
            case 'p':
                s_port = atoi(optarg);
                if (s_port == 0) {
                    usage(argv[0]);
                    return NULL;
                }
                LOGI("Opening loopback port %d\n", s_port);
            break;

            case 'd':
                s_device_path = "/dev/smd0";
                LOGI("Opening tty device %s\n", s_device_path);
            break;

            case 's':
                s_device_path   = optarg;
                s_device_socket = 1;
                LOGI("Opening socket %s\n", s_device_path);
            break;

            default:
                usage(argv[0]);
                return NULL;
        }
    }

    if (s_port < 0 && s_device_path == NULL) {
        usage(argv[0]);
        return NULL;
    }

    pthread_attr_init (&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
    ret = pthread_create(&s_tid_mainloop, &attr, mainLoop, NULL);

    return &s_callbacks;
}
#else /* RIL_SHLIB */
int main (int argc, char **argv)
{
    int ret;
    int fd = -1;
    int opt;

    while ( -1 != (opt = getopt(argc, argv, "p:d:"))) {
        switch (opt) {
            case 'p':
                s_port = atoi(optarg);
                if (s_port == 0) {
                    usage(argv[0]);
                }
                LOGI("Opening loopback port %d\n", s_port);
            break;

            case 'd':
	        			s_device_path = "/dev/smd0";
                LOGI("Opening tty device %s\n", s_device_path);
            break;

            case 's':
                s_device_path   = optarg;
                s_device_socket = 1;
                LOGI("Opening socket %s\n", s_device_path);
            break;

            default:
                usage(argv[0]);
        }
    }

    if (s_port < 0 && s_device_path == NULL) {
        usage(argv[0]);
    }

    RIL_register(&s_callbacks);

    mainLoop(NULL);

    return 0;
}

#endif /* RIL_SHLIB */
