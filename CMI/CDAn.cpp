// CDAn.cpp : Defines the initialization routines for the DLL.
// V1.0	- 2007-90
// V1.1 - 05.08.2011
//			modified CorrectGP1NDL random function

#include "stdafx.h"

#include "LMFPreEventData.h"
#include "CoboldUtilities.h"

#include "CDAn.h"
#include "math.h"
#include "CDAq.h"
#include "LMInfo.h"

#include "UserSHM.h"
#include "UserSP.h"

#ifdef _DEBUG
#define new DEBUG_NEW
#undef THIS_FILE
static char THIS_FILE[] = __FILE__;
#endif

#ifndef _DEBUG
extern "C" IMAGE_DOS_HEADER __ImageBase;
#endif

/////////////////////////////////////////////////////////////////////////////
// CDAnApp
BEGIN_MESSAGE_MAP(CDAnApp, CWinApp)
	//{{AFX_MSG_MAP(CDAnApp)
		// NOTE - the class wizard will add and remove mapping macros here.
		//    DO NOT EDIT what you see in these blocks of generated code!
	//}}AFX_MSG_MAP
END_MESSAGE_MAP()

/////////////////////////////////////////////////////////////////////////////
// CDAnApp construction
CDAnApp theDAnApp;
CUserSpectrum *pDAnUserSP;
CSourceCodeInformation *pCodeInformation;

/////////////////////////////////////////////////////////////////////////////
CString *pDllFilePathName;

typedef SharedClass * (*MyProc4)();
MyProc4 Get_shared_class_instance;

CDAnApp::CDAnApp()
{
	// get the dll's loaded path-file name
	pDllFilePathName = new CString("");
	char *pcStr = new char[MAX_PATH];
	GetModuleFileName((HINSTANCE)&__ImageBase,pcStr,MAX_PATH);
	pDllFilePathName->Append(pcStr);
	if(pcStr) 
	{
		delete[] pcStr; 
		pcStr = nullptr;
	}
}

BOOL CDAnApp::InitInstance()
{
	if(!CWinApp::InitInstance()) 
		return FALSE;

	// prepare user access to certain spectrum commands
	pDAnUserSP = (CUserSpectrum *)new CUserSpectrum();

	// prepare SharedClass and UserSHM 
	this->SharedClassInstance = nullptr;
	this->UserSHM_DLL_is_bound = false;
	this->UserSHM_lib_handle = nullptr;
	BindUserSHMDll();

	// prepare source code information
	pCodeInformation = (CSourceCodeInformation *)new CSourceCodeInformation();
	pCodeInformation->coaCodeInformation.Add(new CCodeInformation("IDS_SOURCE_CPP", "CDAN", "CDAn.cpp"));
	pCodeInformation->coaCodeInformation.Add(new CCodeInformation("IDS_SOURCE_CPP", "DANUTILITIES", "DAnUtilities.cpp"));
	pCodeInformation->coaCodeInformation.Add(new CCodeInformation("IDS_SOURCE_CPP", "STANDARDDAN", "StandardDAn.cpp"));
	pCodeInformation->coaCodeInformation.Add(new CCodeInformation("IDS_SOURCE_CPP", "STDAFX", "StdAfx.cpp"));

	pCodeInformation->coaCodeInformation.Add(new CCodeInformation("IDS_SOURCE_H", "CDAN", "CDAn.h"));
	pCodeInformation->coaCodeInformation.Add(new CCodeInformation("IDS_SOURCE_H", "CDAQ", "CDAq.h"));
	pCodeInformation->coaCodeInformation.Add(new CCodeInformation("IDS_SOURCE_H", "CHECKPROCESS", "CheckProcess.H"));
	pCodeInformation->coaCodeInformation.Add(new CCodeInformation("IDS_SOURCE_H", "COBOLDUTILITIES", "CoboldUtilities.h"));
	pCodeInformation->coaCodeInformation.Add(new CCodeInformation("IDS_SOURCE_H", "LMFPREEVENTDATA", "LMFPreEventData.h"));
	pCodeInformation->coaCodeInformation.Add(new CCodeInformation("IDS_SOURCE_H", "LMINFO", "LMInfo.h"));
	pCodeInformation->coaCodeInformation.Add(new CCodeInformation("IDS_SOURCE_H", "RESOURCE", "resource.h"));
	pCodeInformation->coaCodeInformation.Add(new CCodeInformation("IDS_SOURCE_H", "STDAFX", "StdAfx.h"));
	pCodeInformation->coaCodeInformation.Add(new CCodeInformation("IDS_SOURCE_H", "USERSHM", "UserSHM.h"));
	pCodeInformation->coaCodeInformation.Add(new CCodeInformation("IDS_SOURCE_H", "USERSP", "UserSP.h"));

	return TRUE;
}

__int32 CDAnApp::ExitInstance()
{
	// release UserSP
	if(pDAnUserSP)
	{
		delete pDAnUserSP;
		pDAnUserSP = nullptr;
	}

	// release CodeInformation
	if(pCodeInformation)
	{
		pCodeInformation->coaCodeInformation.RemoveAll();
		pCodeInformation->coaCodeInformation.FreeExtra();
		delete pCodeInformation;
		pCodeInformation = nullptr;
	}
	
	// release UserSHM
	if(this->UserSHM_lib_handle) 
	{
		FreeLibrary(UserSHM_lib_handle);
		UserSHM_lib_handle = 0;
		UserSHM_DLL_is_bound = false;
	}
	return CWinApp::ExitInstance();
}

/////////////////////////////////////////////////////////////////////////////
// Local variables used for Event Time functions
double _dOldEventTime;
double _dStartEventTime;

bool CDAnApp::BindUserSHMDll() 
{
	if(UserSHM_DLL_is_bound) 
		return true;
	if(!UserSHM_lib_handle)
	{
		if(IsProcess64())
			UserSHM_lib_handle = LoadLibrary("UserSHM_x64.dll");
		else
			UserSHM_lib_handle = LoadLibrary("UserSHM_x86.dll");
	}

	if(UserSHM_lib_handle) 
	{
		Get_shared_class_instance = (MyProc4)GetProcAddress(UserSHM_lib_handle,"SHMGetSharedClassInstance");
		SharedClassInstance = Get_shared_class_instance();
		if(SharedClassInstance) 
			UserSHM_DLL_is_bound = true; 
		else 
			UserSHM_DLL_is_bound = false;
		if(SharedClassInstance) 
		{
			SharedClassInstance->csDAnNameAndPath = CString(theDAnApp.m_pszHelpFilePath);
			SharedClassInstance->csDAnNameAndPath = SharedClassInstance->csDAnNameAndPath.Left(SharedClassInstance->csDAnNameAndPath.GetLength()-3);
			SharedClassInstance->csDAnNameAndPath += CString("dll");
		}
	} 
	else 
	{
		if(IsProcess64())
			AfxMessageBox(CString("UserSHM_x64.dll not found by DAn"));
		else
			AfxMessageBox(CString("UserSHM_x86.dll not found by DAn"));
	}

	return UserSHM_DLL_is_bound;
}

//bool CDAnApp::UnBindUserSHMDll()
//{
//    bool bReturn = true;
//
//    if(UserSHM_lib_handle)
//        bReturn = FreeLibrary(UserSHM_lib_handle) ? true : false;
//    if(bReturn)
//        UserSHM_lib_handle = NULL;
//    return bReturn;
//}

/////////////////////////////////////////////////////////////////////////////
// DAnGetDllPathName
// -----------------
// returns name and path of the loaded dll
CString &DAnGetDllPathName()
{
	return *pDllFilePathName;
}

/////////////////////////////////////////////////////////////////////////////
// GetDeltaEventTime
// -----------------
// Calculate the time between two events
// returns time in seconds (always 0 for the first event!)
double GetDeltaEventTime(LMFPreEventData &preEventData, CDoubleArray &Parameter)
{
	LARGE_INTEGER liTime = preEventData.TimeStamp;

	double dTimeScaling = Parameter[5];	// frequency, in counts per second, of the high-resolution performance counter
	double dEventTime = (double)liTime.QuadPart;
	dEventTime /= dTimeScaling;
	double dDeltaEventTime = _dOldEventTime != 0.0 ? dEventTime - _dOldEventTime : 0.0;
	_dOldEventTime = dEventTime;
	
	return dDeltaEventTime;
}

/////////////////////////////////////////////////////////////////////////////
// GetEventTime
// ------------
// Calculate the time between the actual event and the first event
// returns time in seconds
double GetEventTime(LMFPreEventData &preEventData, CDoubleArray &Parameter)
{
	LARGE_INTEGER liTime = preEventData.TimeStamp;

	double dTimeScaling = Parameter[5];	// frequency, in counts per second, of the high-resolution performance counter
	double dEventTime = (double)liTime.QuadPart;
	dEventTime /= dTimeScaling;
	if(_dStartEventTime == 0)
		_dStartEventTime = dEventTime;
	return (dEventTime - _dStartEventTime);
}

/////////////////////////////////////////////////////////////////////////////
// CorrectGP1NDL
// -------------
// corrects the differential nonlinearity of the GP1/HM1 module
// returns the corrected 
double CorrectGP1NDL(double dChannel, double dCorrectionValue)
{
	double dChStart = dChannel;
	double dOldChannel = dChannel;
	__int32 iRand;
	double dRand;
	bool bMoved = false;
	if(fmod(dChannel,2.) == 0)
	{
		iRand = rand();
		dRand = (double)iRand / (double)(RAND_MAX+1);
		if(dRand <= dCorrectionValue)
		{
			dChannel += 1.;
			bMoved = true;
		}
	}
	if(bMoved)
		return dChannel;
	else
		return dOldChannel;
}

CDAN_API CSourceCodeInformation* DAnGetSourceCodeInformation()
{
	return pCodeInformation;
}