// LMInfo.h
// Informations file to control List-Mode Read
#pragma once

#define LM_FILE_VERSION		0x74656			// only 32 bit for int values
#define LM_FILE_VERSION9	0x74657			// partially 64 bit for int values (since 9.1.808.1)

#define LM_READFILE			-0x00000000
#define LM_NOFILEOPEN		-0x00000001
#define LM_CLOSEFILE		-0x00000002
#define LM_STARTFILE		-0x00000004
#define LM_HOLDFILE			-0x00000008
#define LM_ENDFILE			-0x00000010
#define LM_REWINDFILE		-0x00000020
#define LM_CLOSEING			-0x00000040

#define LM_HARDWARE			0x00000001
#define LM_FILEREAD			0x00000002
#define LM_HARDWAREWRITE	0x00000004
#define LM_SKIPINSERT		0x00000008

#define LMS_HRUNNING		0x00000004
#define LMS_FRUNNING		0x00000003
#define LMS_RUNNING			0x00000002
#define LMS_PAUSED			0x00000001
#define LMS_NONE			0x00000000

#define LMW_NOTSET			0x00000000
#define LMW_EOF				0x00000001
#define LMW_TIME			0x00000002
#define LMW_COUNTS			0x00000003
#define LMW_UNDEF			0xffffffff

// Data types possible in DAq/DAn
#define DT_NOTSET			0x00000000
#define DT_CHANNEL			0x00000001
#define DT_TIMEINPS			0x00000010
#define DT_TIMEINNS			0x00000011

#define DAQ_ID_RAW			0x000000		// for RAW (no Data)
#define DAQ_ID_HM1			0x000001		// for HM1 (single)
#define DAQ_ID_TDC8			0x000002		// for TDC8/ISA/PCI
#define DAQ_ID_CAMAC		0x000003		// for CAMAC
#define DAQ_ID_2HM1			0x000004		// for 2 HM1
#define DAQ_ID_2TDC8		0x000005		// for 2 TDC8
#define DAQ_ID_HM1_ABM		0x000006		// for HM1 (Advanced Burst Mode)
#define DAQ_ID_HM1_LR		0x000007		// for HM1 (Long Range Mode)
#define DAQ_ID_HPTDC		0x000008		// for HPTDC (TillDC)
#define DAQ_ID_TCPIP		0x000009		// for TCPIP (not supported yet)
#define DAQ_ID_HPTDCRAW		0x000010		// for HPTDC (TillDC) writing RAW data
#define DAQ_ID_FADC8		0x000011		// for FADC8
#define DAQ_ID_FADC4		0x000012		// for FADC4

// Source Code Included Flags
//	if LM_FILE_VERSION9 upper bits indicate presence of source code
#define DAQ_SOURCE_CODE		0x80000000
#define DAN_SOURCE_CODE		0x40000000
#define CCF_HISTORY_CODE	0x20000000

#define MASK_LMF_FILEVERSION	(~(DAQ_SOURCE_CODE|DAN_SOURCE_CODE|CCF_HISTORY_CODE))

// LMF main header structure
typedef struct struct_LMFMAINHEADER {
	unsigned __int32	LMHeaderVersion;
	unsigned __int32	LMDataFormat;
	unsigned __int64	LM64NumberOfCoordinates;
	unsigned __int64	LM64HeaderSize;
	unsigned __int64	LM64UserDefinedHeaderSize;
	unsigned __int64	LM64NumberOfEvents;
	CTime			LMStartTime;
	CTime			LMStopTime;
	CString			LMVersionString;
	CString			LMFilePathName;
	CString			LMComment;
} LMFMAINHEADER;

