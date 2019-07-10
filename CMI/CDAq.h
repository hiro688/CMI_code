// CDAq.h : main header file for the CDAq DLL
//
#pragma once

#ifndef __AFXWIN_H__
	#error include 'stdafx.h' before including this file for PCH
#endif

#include "resource.h"		// main symbols
//#include "..\CoboldUtilities\CoboldUtilities.h"
//#include "..\HM1\HM1.h"

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

#ifdef CDAQ_EXPORTS
#define CDAQ_API __declspec(dllexport)
#else
#define CDAQ_API __declspec(dllimport)
#endif

#define INCLUDE_HARDWARE_SUPPORT

// definitions for main program event data format
#define LM_BYTE					1	//  8bit integer
#define LM_SHORT				2	// 16bit integer
#define LM_LONG					3	// 32bit integer
#define	LM_FLOAT				4   // 32bit IEEE float
#define LM_DOUBLE				5	// 64bit IEEE float
#define LM_CAMAC				6	// 24bit integer
#define LM_DOUBLELONG			7	// 64bit integer
#define LM_SBYTE				8	// signed 8bit integer
#define LM_SSHORT				9	// signed 16bit integer
#define LM_SLONG				10	// signed 32bit integer
#define LM_SDOUBLELONG			11	// signed 64bit integer
#define LM_LASTKNOWNDATAFORMAT	LM_SDOUBLELONG
#define LM_USERDEF				-1	// user will handle the reading 
									// of file and filling of EventData Array
									// except reading the main header file

class LMFPreEventData;
class CDoubleArray;

CDAQ_API LPCTSTR DAqGetInformationString();
CDAQ_API LPCTSTR DAqGetLastLMFName(CArchive *pAr = nullptr);	// if pAr != nullptr then get the function Name 
																//    (call only in DAqLMFWriteUserHeader or DAqLMFReadUserHeader
																// else get last stored value
CDAQ_API CTime *DAqGetLastStartTime();
CDAQ_API void DAqSetLMHeaderVersion(unsigned __int32 _ui32LMHeaderVersion);

CDAQ_API __int64 DAqInitialize(CDoubleArray &Parameter, unsigned __int32 *pDataFormat, __int64 MaxEvents);
CDAQ_API bool DAqFinalize(CDoubleArray &Parameter);

CDAQ_API bool DAqLMFWriteUserHeader(CArchive *pAr, CDoubleArray &Parameter, unsigned __int64 *pLMUserHeaderLength = nullptr);
CDAQ_API bool DAqLMFReadUserHeader(CArchive *pAr, CDoubleArray &Parameter, unsigned __int64 LMUserHeaderLength);

CDAQ_API bool DAqOnlineFinalize(CArchive *pAr, CDoubleArray &Parameter);
CDAQ_API bool DAqOfflineFinalize(CArchive *pAr, CDoubleArray &Parameter);

CDAQ_API __int32 DAqOnlineReadEvent(CArchive *pAr, CDoubleArray &EventData, CDoubleArray &Parameter, LMFPreEventData &preEventData);
CDAQ_API __int32 DAqOfflineReadEvent(CArchive *pAr, CDoubleArray &EventData, CDoubleArray &Parameter, LMFPreEventData &preEventData);

/////////////////////////////////////////////////////////////////////////////
// CDAqApp
// See CDAq.cpp for the implementation of this class
//

class CDAqApp : public CWinApp
{
public:
	CDAqApp();

// Overrides
	// ClassWizard generated virtual function overrides
	//{{AFX_VIRTUAL(CDAqApp)
	//}}AFX_VIRTUAL

	//{{AFX_MSG(CDAqApp)
		// NOTE - the ClassWizard will add and remove member functions here.
		//    DO NOT EDIT what you see in these blocks of generated code !
	//}}AFX_MSG
	DECLARE_MESSAGE_MAP()
};

/////////////////////////////////////////////////////////////////////////////
#ifdef __cplusplus
}
#endif

