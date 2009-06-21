//
// Convert CDMA SMS to GSM and vice versa.
// By Martin Johnson <M.J.Johnson@massey.ac.nz>
// GPL
//
#include <stdio.h>
#include <string.h>
#include "sms_gsm.h"

#define LOG_TAG "SMS_RIL"
#include <utils/Log.h>

int hex2int(char c) {
	if(c>'9') return c-'A'+10;
	return c-'0';
}

int getbit(char *s,int b) {
	int byte=b/4;
	int bit=b%4;
	
	int data=hex2int(s[byte]);
	if(data&(1<<(3-bit))) return 1;
		else return 0;
}

const char hextable[17]="0123456789ABCDEF";

void setbit(char *s,int b, int val) {
	int byte=b/4;
	int bit=b%4;
	
	s[byte]=hextable[hex2int(s[byte]) | (val<<(3-bit))] ;
}

int getbits(char *s,int startbit,int nbits) {
	int val=0;
	int i;

	for(i=0;i<nbits;i++)
		val = val | (getbit(s,startbit+i)<<(nbits-i-1));
	return val;
}

void setbits(char *s,int startbit,int nbits,int val) {
	int i;

	for(i=0;i<nbits;i++)
		setbit(s,startbit+i,(val>>(nbits-i-1))&1);
}

const char decode_table[17]=".1234567890*#...";

void decode_number(char *msg, int length, char *no) {
	
	int ndigits=getbits(msg,2,8);
	int j,digit;

	for(j=0;j<ndigits;j++) 
		*no++=decode_table[getbits(msg,10+j*4,4)];
	*no=0;
}

int encode_digit(int d) {
	int i;
	for(i=0;i<16;i++)
		if(decode_table[i]==d)
			return i;
	return 0;
}		

int encode_number(char *msg, char *no) {
	unsigned int i;
	int digit;
	
	setbits(msg, 0, 2, 0);
	setbits(msg, 2, 8, strlen(no));
	for(i=0;i<strlen(no);i++)
		setbits(msg,10+i*4, 4, encode_digit(no[i]));
	return (10+i*4+7)/8;
}

void get_code_and_length(char *msg, int *code, int *length) {
	*code=hex2int(msg[0])*16+hex2int(msg[1]);
	*length=hex2int(msg[2])*16+hex2int(msg[3]);
}

void decode_bearer_data(char *msg, int length, char *message, int *is_vm) {
    int i=0,j;
    int code,sublength;

    while(i<length) {
        get_code_and_length(msg+i*2,&code,&sublength);
        if(code==1) {
            int encoding=getbits(msg+i*2+4,0,5);
            int nchars=getbits(msg+i*2+4,5,8);
                if(encoding==2 || encoding==3) {
                    for(j=0;j<nchars;j++)
                        *message++=getbits(msg+i*2+4,13+7*j,7);
                } else 
                if(encoding==8) {
               for(j=0;j<nchars;j++)
                  *message++=getbits(msg+i*2+4,13+8*j,8);
            } else {
                    strcpy(message,"bad SMS encoding");
                    message+=16;
                }
            *message=0;
        } else if (code == 11 && sublength == 1) {
            int msgs;
            if (is_vm) {
                *is_vm = 1;
                msgs = hex2int(msg[i*2+4])+16*hex2int(msg[i*2+5]);
                if (msgs)
                    *is_vm |= 0x10;
            }
        }
        i+=sublength+2;
    }
    
}

int encode_bearer_data(char *msg, char *data) {
	int msgid=0;
	unsigned int i;
        int b;
	char *start=msg;
	
	for(i=0;i<strlen(data);i++)
		msgid+=data[i];
		
	setbits(msg,0,8,0); // message id
	setbits(msg,8,8,3); // 3 bytes
	setbits(msg,16,4,2); // 2 means send
	setbits(msg,20,16,msgid); // use message sum for id
	msg+=10;
	setbits(msg,0,8,01); // user data
	setbits(msg,16,5,02); // set encoding
	setbits(msg,21,8,strlen(data)); // length
	b=29;
	for(i=0;i<strlen(data);i++) {
		setbits(msg,b,7,data[i]);
		b=b+7;
	}
	setbits(msg,8,8,(b+7)/8-2);
	msg=msg+2*((b+7)/8);
	setbits(msg,0,24,0x80100);
	setbits(msg,24,24,0x0D0100);
	msg=msg+12;
	return (msg-start)/2;
}

void decode_cdma_sms(char *pdu, char *from, char *message, int *is_vm) {
    unsigned int i=1;
    int code,length;
    strcpy(from,"000000"); // in case something fails
    strcpy(message,"UNKNOWN"); 
    
    if (is_vm)
        *is_vm = 0;

    while(i*2<strlen(pdu)) {
        get_code_and_length(pdu+i*2,&code,&length);
        if(code==2) // from
            decode_number(pdu+i*2+4,length,from);
        if(code==8) // bearer_data
            decode_bearer_data(pdu+i*2+4,length,message,is_vm);
        i+=length+2;
    }
}

void encode_cdma_sms(char *pdu, char *to, char *message) {
	int i;
	int length;
	
	if(strlen(message)>160) LOGE("Error: Message String too long");
	for(i=0;i<512;i++)
		pdu[i]='0';
	setbits(pdu,0,16,0);
	setbits(pdu,16,24,0x021002);
	pdu=pdu+10;
	setbits(pdu,0,8,0x04);
	length=encode_number(pdu+4, to);
	setbits(pdu,8,8,length);
	pdu=pdu+length*2+4;
	setbits(pdu,0,24,0x060100);
	pdu=pdu+6;
	setbits(pdu,0,8,0x08);
	length=encode_bearer_data(pdu+4, message);
	if(length>255) LOGE("Error: Message Hex too long");
	setbits(pdu,8,8,length);
	pdu=pdu+length*2+4;
	*pdu=0;
}

char **cdma_to_gsmpdu(char *msg) {
	char from[256];
	char message[256];
	static char hexpdu[1024];
	static char *hexpdus[16];
	int i=0;
        int is_vm=0;
	decode_cdma_sms(msg,from,message,&is_vm);
//	if(strlen(message)>=160) message[159]=0;
	LOGD("CDMA Message:%s From:%s\n",message,from);
	SmsAddressRec smsaddr;
	SmsTimeStampRec smstime;
        if (is_vm) {
            /* voicemail notifications must have a 4 byte address */
            if (is_vm & 0x10) {
                /* set message waiting indicator */
                strcpy(from, "1100");
            } else {
                /* clear message waiting indicator */
                strcpy(from, "0100");
            }
        }
	sms_address_from_str(&smsaddr,from,strlen(from));
        if (is_vm) {
            /* voicemail notifications have a clear bottom nibble in toa
             * and an alphanumeric address type */
            smsaddr.toa = 0xd0;
        }
	sms_timestamp_now(&smstime);
	SmsPDU *pdu=smspdu_create_deliver_utf8((const unsigned char *)message,strlen(message),&smsaddr,&smstime);
	//hexpdu=malloc(512);
	char *s=hexpdu;
        while(*pdu) {
                smspdu_to_hex(*pdu, s,512);
                hexpdus[i]=s;
                s=s+strlen(s)+2;
                smspdu_free(*pdu);
                i++;
                pdu++;
        }
	hexpdus[i]=0;
	return hexpdus;
}

char *gsm_to_cdmapdu(char *msg) {
	char to[256];
	char message[256];
	static char hexpdu[512];
	SmsAddressRec smsaddr;
	sms_address_from_str(&smsaddr,"000000",6);

	SmsPDU pdu=smspdu_create_from_hex( msg, strlen(msg) );
	if(smspdu_get_receiver_address(pdu,&smsaddr)<0) {
		LOGE("Error: no receiver address");
		smspdu_get_sender_address(pdu,&smsaddr);
	}
	sms_address_to_str(&smsaddr,to,256);
	int length=smspdu_get_text_message(pdu, message, 256);
	message[length]=0;
	smspdu_free(pdu);
	LOGD("GSM Message:%s To:%s\n",message,to);
	encode_cdma_sms(hexpdu,to,message);
	return hexpdu;
}

/*
int main() {
	char  msg3[]="00000210020206026886089E9C08220003145C10010E10748CBB366F41930F2D9A77674003060805272056520C000D0100";
	char  msg2[]="0000021002040401222140060100081300032733A0010610253A93E8000801000D0100"; // cdma
	char  msg1[]="0001000481885800000453ea130a"; // gsm from android
	char  msg6[]="002006810000000000805003316223840453ea130a";
//					002006810000000000805003319074840453ea130a
					//  0001002006810000000000805003314005840453ea130a
	char  msg[]="00010004815454000004d4f29c0e";
	char  msg4[]="000100069110090000F111000A9210299232900000AAA06374580E529DE7ED08FD1D1993DB6138B98E1AA3C37290AA3D3FA740000508041AA3C37210FD0D90D56C809D0204028DD16139A85D9ECFC3E7324056B301760A100834A787E9E931688C0ECB41E8321E4EAE036A311960A7008140D3F63C4826CBCBF3B9B43C06CDDBF330992CDF2914201068DA9E438955109C5CEFCDDB7338B91E19CBCB617A396296BFDB";
//	char *gsmpdu=cdma_to_gsmpdu(msg3);	
//	printf("GSM PDU=%s\n",gsmpdu);
	char msg5[512];
	
	encode_cdma_sms(msg5,"8885","0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789");
	printf("CDMA PDU=%s\n",msg5);

	char *gsmpdu=cdma_to_gsmpdu(msg5);
   printf("GSM PDU=%s\n",gsmpdu);
//	encode_gsm_sms(gsmpdu,"8885","STOP");

	char *cdmapdu=gsm_to_cdmapdu(msg1);
	printf("CDMA PDU=%s\n",cdmapdu);

	gsmpdu=cdma_to_gsmpdu(cdmapdu);
	printf("GSM PDU=%s\n",gsmpdu);
}
*/
