// UserSP.h : main header file for the UserSP DLL
//

#pragma once

#ifndef __AFXWIN_H__
	#error "include 'stdafx.h' before including this file for PCH"
#endif

#include "resource.h"		// main symbols

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

#ifdef USERSP_EXPORTS
#define USP_API __declspec(dllexport)
#include "TUserSP.h"
#else
#define USP_API __declspec(dllimport)
#endif

#ifndef X_AXIS
#define X_AXIS          0x00000001
#endif
#ifndef Y_AXIS
#define Y_AXIS          0x00000002
#endif

class CDoubleArray;

// CUserSPApp
// See UserSP.cpp for the implementation of this class
//
class CUserSPApp : public CWinApp
{
public:
	CUserSPApp();

// Overrides
public:
	BOOL InitInstance();

// Possible Spectrum calling functions...
public:

	DECLARE_MESSAGE_MAP()
};

class CCoboldDocSpectrum;
class CParameter;
class CtUserSpectrum;

class USP_API CUserSpectrum
{
// constructor / destructor
public: 
	CUserSpectrum();
	CUserSpectrum(void *pCDoc);
	virtual ~CUserSpectrum();

// implementation
public:
	// spectra math functions
	void AddOneAt(__int32 iSpNr, double dChannel);
	void AddOneAt(__int32 iSpNr, double dChannelX, double dChannelY);
	void AddValueAt(__int32 iSpNr,double dChannel, double dValue);
	void AddValueAt(__int32 iSpNr,double dChannelX, double dChannelY, double dValue);
	void SetValueAt(__int32 iSpNr,double dChannel, double dValue);
	void SetValueAt(__int32 iSpNr,double dChannelX, double dChannelY, double dValue);
	double GetValueAt(__int32 iSpNr,double dChannel);
	double GetValueAt(__int32 iSpNr,double dChannelX, double dChannelY);
	double GetBinValueAt(__int32 iSpNr, __int64 iChannel);
	double GetBinValueAt(__int32 iSpNr, __int64 iChannelX, __int64 iChannelY);
	void SetBinValueAt(__int32 iSpNr, __int64 iChannel, double dValue);
	void SetBinValueAt(__int32 iSpNr, __int64 iChannelX, __int64 iChannelY, double dValue);
	bool GetHistogramDataArray(__int32 iSpNr, double *pData, __int64 MaxIndex);
	bool SetHistogramDataArray(__int32 iSpNr, double *pData, __int64 MaxIndex);
	bool ClearSpectrum(__int32 iSpNr);

	// spectra information functions
	//		index
	__int64 GetBinIndexX(__int32 iSpNr, double Channel);
	__int64 GetBinIndexY(__int32 iSpNr, double Channel);
	double GetBinChannelX(__int32 iSpNr, unsigned __int64 Channel);
	double GetBinChannelY(__int32 iSpNr, unsigned __int64 Channel);

	//		bins
	__int64 GetNumberOfXBins(__int32 iSpNr);
	__int64 GetNumberOfYBins(__int32 iSpNr);
	//		diverse information
	__int32 FindSpectrum(char *pcSpName);
	__int64 GetDisplayedSpectrumNumber();
	CString GetDisplayedSpectrumName();
	CString GetSpectrumName(__int32 iSpNr);
	__int32 GetSpectrumType(__int32 iSpNr, bool bDisplayError);
	double GetBinSizeX(__int32 iSpNr);
	double GetBinSizeY(__int32 iSpNr);
	void GetSpectrumDataInformation(__int32 iSpNr, double* &pdDataPointer, unsigned long &ulDimX, unsigned long &ulDimY);
	void SetGaussFitValues(__int32 iSpNr, double x0, double y0, double Sigma, double YOffset, double lowLimit, double highLimit, double usedLowLimit, double usedHighLimit);
	bool GetMultiFileInformation(__int32 &i32ActualFileNumber, CString &csActualFilePathName, CString &csBaseFilePathName, __int32 &i32StartNumber, __int32 &i32EndNumber, bool &bIsFirstFile, bool &bIsLastFile);
	void SignalStopMultiFile();
	void SignalStop();

	//		coordinate
	__int32 GetCoordinateIndexByName(char *pcCoordinateName);
	char * GetCoordinateNameByIndex(__int32 i32Index);
	// marker/cursor functions
	void GetXYPosition(double &xRet, double &yRet, __int32 AxisFlags);
	void GetXYCursor(double &xRet, double &yRet, bool bSnap);
	void GetXYBoxCursor(double &xStartRet, double &yStartRet, double &xEndRet, double &yEndRet, bool bSnap);
	void SetMarker(CString csType,CDoubleArray &InputData);
	double GetBinsizeX(__int32 iSpNr);
	double GetBinsizeY(__int32 iSpNr);

	// list mode information
	LMFMAINHEADER GetActualLMFMainHeader();

protected:
	CCoboldDocSpectrum *pSP;
//#ifdef USERSP_EXPORTS
	CtUserSpectrum *ptUserSp;
//#endif
public:
};

#ifdef __cplusplus
}
#endif
