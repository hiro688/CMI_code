#pragma once

#ifndef LMFPreEventDataInclude
#define LMFPreEventDataInclude

#ifdef COBOLDUTILITIES_EXPORTS
	#define COBOLDUTILITIES_APP __declspec(dllexport)
#else
	#define COBOLDUTILITIES_APP __declspec(dllimport)
#endif

// LMF information of the actual/last NEW command
typedef struct struct_NEWInformation {
	bool	bHardware;		// flag for Type of the DAQ mode
	CString FileName;		// string filename single file
	CString FileBase;		// string filename base multi file
	bool	bAnalysis;		// flag for using the Analysis
	__int64 StartAtEvent;	// start at Event
	__int64 maxEvents;		// maxEvents per file from StartAtEvent
	CString Comment;		// file comment
	__int32 startBase;		// multi file mode start number
	__int32 endBase;		// multi file mode end number
	bool	bAutoClear;		// flag for using the auto clear between multi file LMFs
	bool	bAutoSave;		// flag for using the auto save between multi file LMFs
	CString CCFBase;		// string CCFBase name multi file

	bool	bMultiFile;		// flag for using multi file mode
	bool	bOverwriteFiles;// flag for overwriting files
	unsigned __int32 firstFoundNumber;	// for MF it's the first found file number
	unsigned __int32 lastFoundNumber;	// for MF it's the last found file number (to detect last file action)
	bool	bIsFileOnNetwork;	// flag for files on network paths
	CTimeSpan maxTime;		// maximum time per file from StartAtEvent time
	bool	bIsEventMode;	// flag indicating event or time information as end condition for LMF
} NEWInformation;

class COBOLDUTILITIES_APP LMFPreEventData
{
public:
	LMFPreEventData();
	virtual ~LMFPreEventData();
// data
	// hdr1 = EventMarker + EventLength
	//		bit 63..56		always 0xff
	//		bit 55..00		EventLegth in Bytes of this event
	// hdr2
	//		bit 63..00		event counter
	__int64	hdr1;
	__int64 hdr2;
	LARGE_INTEGER TimeStamp;	// low part for 32 bit, high and low part for 64 bit Timestamp
};

#endif