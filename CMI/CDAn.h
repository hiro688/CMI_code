// CDAn.h : main header file for the CDAn DLL
// V5.14
#pragma once

#ifndef __AFXWIN_H__
	#error include 'stdafx.h' before including this file for PCH
#endif

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

#ifdef CDAN_EXPORTS
#define CDAN_API __declspec(dllexport)
#else
#define CDAN_API __declspec(dllimport)
#endif

class SharedClass;
class CDoubleArray;
class CSourceCodeInformation;
class CDAnApp;

extern CDAnApp theDAnApp;

// no file support during AnalysisInitialize
// no file support during AnalysisGetInformationString

// 
// I M P O R T A N T
//
// If you use CArchive or something equivalent 
// then flush first any data of the file before 
// you call any function other than reading from the
// file or flushing the data otherwise you risk a
// misaligned file!

CDAN_API LPCTSTR AnalysisGetInformationString();
CDAN_API __int32 AnalysisInitialize(CDoubleArray &EventData, CDoubleArray &Parameter, CDoubleArray &WeighParameter);
CDAN_API __int32 AnalysisProcessEvent(CDoubleArray &EventData, CDoubleArray &Parameter, CDoubleArray &WeighParameter, LMFPreEventData &preEventData);
CDAN_API __int32 AnalysisFinalize(CDoubleArray &EventData,CDoubleArray &Parameter, CDoubleArray &WeighParameter);

CDAN_API CSourceCodeInformation* DAnGetSourceCodeInformation();

/////////////////////////////////////////////////////////////////////////////
// CDAnApp
// See CDAn.cpp for the implementation of this class
//

class CDAnApp : public CWinApp
{
public:
	CDAnApp();
// Overrides
	BOOL InitInstance();
	__int32 ExitInstance();

	bool BindUserSHMDll();
	HMODULE UserSHM_lib_handle;
	SharedClass * SharedClassInstance;
	bool UserSHM_DLL_is_bound;

	// ClassWizard generated virtual function overrides
	//{{AFX_VIRTUAL(CDAnApp)
	//}}AFX_VIRTUAL

	//{{AFX_MSG(CDAnApp)
		// NOTE - the ClassWizard will add and remove member functions here.
		//    DO NOT EDIT what you see in these blocks of generated code !
	//}}AFX_MSG
	DECLARE_MESSAGE_MAP()
};

extern double _dOldEventTime;
extern double _dStartEventTime;
extern CString &DAnGetDllPathName();

double GetDeltaEventTime(LMFPreEventData &preEventData,CDoubleArray &Parameter);
double GetEventTime(LMFPreEventData &preEventData,CDoubleArray &Parameter);
double CorrectGP1NDL(double dChannel,double dCorrectionValue);


/////////////////////////////////////////////////////////////////////////////
#ifdef __cplusplus
}
#endif

