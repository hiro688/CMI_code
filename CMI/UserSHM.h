// UserSHM.h : main header file for the UserSHM DLL
//

#pragma once

#ifndef __AFXWIN_H__
	#error "include 'stdafx.h' before including this file for PCH"
#endif

#include "resource.h"		// main symbols

// CUserSHMApp
// See UserSHM.cpp for the implementation of this class
//
class CUserSHMApp : public CWinApp
{
public:
	CUserSHMApp();

	// Overrides
public:
	virtual BOOL InitInstance();
	virtual __int32 ExitInstance();

	DECLARE_MESSAGE_MAP()
};

#ifdef __cplusplus
extern "C" 
{
#endif /* __cplusplus */

	#ifdef USERSHM_EXPORTS
	#define USHM_API __declspec(dllexport)
	#else
	#define USHM_API __declspec(dllimport)
	#endif

	//////////////////////////////////////////////////////////////////////////
	// Forward declarations
	//////////////////////////////////////////////////////////////////////////

	class CDoubleArray;
	class CUserSpectrum;
	class CCoboldParser;

#define SHAREDCLASS_ARRAYSIZE 80

	/////////////////////////////////////////////////////////
	// SharedClass 

	class USHM_API SharedClass
	{
	public:
		SharedClass();
		~SharedClass();

		volatile double rate;
		volatile bool bDAqIsRunningOnline;
		volatile bool bDAqIsRunningOffline;
		volatile bool bDAnIsRunning;
		volatile bool bRequestStopDAq;
		CString csDAqNameAndPath;
		CString csDAnNameAndPath;

		__int16 *adc_trace[SHAREDCLASS_ARRAYSIZE];
		__int32 adc_trace_length[SHAREDCLASS_ARRAYSIZE];
		__int64 adc_trace_absolute_timestamp_ps[SHAREDCLASS_ARRAYSIZE];
		void *adc_peak_infos_array;
		__int32 adc_peak_infos_array_max_nof_hits;

		void * UserSHM_pointer1;
		void * UserSHM_pointer2;
		void * UserSHM_pointer3;
		void * UserSHM_pointer4;
	};

	//////////////////////////////////////////////////////////////////////////
	// Exported / Imported functions
	//////////////////////////////////////////////////////////////////////////

	USHM_API SharedClass *SHMGetSharedClassInstance(void);

	#ifdef USERSHM_EXPORTS
	USHM_API bool DoFunction(CString csInput[],unsigned __int32 ui32InputMaximumIndex, unsigned __int32 ui32WordCount);
	#endif

	extern USHM_API SharedClass *SharedClassInstance;

#ifdef __cplusplus
}
#endif
