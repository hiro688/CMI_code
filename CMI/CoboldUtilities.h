// CoboldUtilities.h : main header file for the COBOLDUTILITIES DLL
//

#ifndef __AFXWIN_H__
	#error include 'stdafx.h' before including this file for PCH
#endif

#include "resource.h"		// main symbols

#define COMPRESSIONTYPE_UNDEFINED	-1
#define COMPRESSIONTYPE_NONE		0
#define COMPRESSIONTYPE_GZIP		1
#define COMPRESSIONTYPE_DEFLATE		2

/////////////////////////////////////////////////////////////////////////////
// CCoboldUtiltiesApp
// See CoboldUtilities.cpp for the implementation of this class
//
#ifndef CCOBOLDUTILITIESAPP_DEF
#define CCOBOLDUTILITIESAPP_DEF

class CCoboldUtiltiesApp : public CWinApp
{
public:
	CCoboldUtiltiesApp();
	~CCoboldUtiltiesApp();

// Overrides
	// ClassWizard generated virtual function overrides
	//{{AFX_VIRTUAL(CCoboldUtiltiesApp)
	//}}AFX_VIRTUAL

	//{{AFX_MSG(CCoboldUtiltiesApp)
		// NOTE - the ClassWizard will add and remove member functions here.
		//    DO NOT EDIT what you see in these blocks of generated code !
	//}}AFX_MSG
	DECLARE_MESSAGE_MAP()
};

#include "CheckProcess.h"

#ifdef COBOLDUTILITIES_EXPORTS
#define COBOLDUTILITIES_APP __declspec(dllexport)
#else
#define COBOLDUTILITIES_APP __declspec(dllimport)
#endif

/////////////////////////////////////////////////////////////////////////////
// ATARI Time structure
typedef struct 
{	
	unsigned short 		hsec	: 5;
	unsigned short 		min		: 6;
	unsigned short 		hour	: 5;
}ATime;

typedef struct 
{	
	unsigned short 		day		: 5;
	unsigned short 		month	: 4;
	unsigned short 		year	: 7;
}ADate;

typedef struct 
{
	ATime 		time;	
	ADate 		date;
}ADateTime;

typedef ULONGLONG (*dllGetTickCounts64)();

class COBOLDUTILITIES_APP CNumberTesting
{
public:
	// Construction
	CNumberTesting();
	~CNumberTesting();

	// Implementation
	bool IsNaN(double val);
	bool IsInfinity(double val);
	bool IsPositiveInfinity(double val);
	bool IsNevativeInfinity(double val);
	bool IsNaNorInfinity(double val);
};

class COBOLDUTILITIES_APP CFileIOHelper
{
public:
	// Construction
	CFileIOHelper(void);
	virtual ~CFileIOHelper(void);
protected:
	void *m_pFileIoHelper;
	CString m_csRet;
	
public:
	// Implementation
	CString& GetFileName(CString PathName);
	CString& GetFileName(CString PathName, bool &displayError);
	CString& GetFileNameWithoutExtension(CString PathName);
	CString& GetFileNameWithoutExtension(CString PathName, bool &displayError);
	CString& GetPath(CString PathName);
	CString& GetPath(CString PathName, bool &displayError);
	CString& GetExtension(CString PathName);
	CString& GetExtension(CString PathName, bool &displayError);
	bool FileExists(CString PathName);
	bool DirectoryExists(CString Path);
	bool DirectoryCreate(CString Path);
	void ShowInformationForm(CString Title, CString Data, bool holdFlag = true);
	void CloseInformationForm();
	CString& SearchFilename(CString baseName, CString extensionName, CString x86Extension, CString x64Extension, bool forceRightOS);
	CString& GetSpecialFolder(CString FolderName);
	bool FileCopy(CString To, CString From);
	bool IsReadOnly(CString PathName);
	bool FileDelete(CString PathName);
	bool CreateLockFile(CString PathName);
	bool AppendTextToLockFile(CString PathName, CString Text);
};

// This class is exported from the CoboldSecurity.dll
//template<class double, class double> 
class COBOLDUTILITIES_APP CDoubleArray : public CObject
{
public:
	DECLARE_SERIAL(CDoubleArray)

// Construction
	CDoubleArray();
	CDoubleArray(__int64 NumberOfElements);
	CDoubleArray(__int64 NumberOfXElements, __int64 NumberOfYElements);

// Attributes
	inline __int64 GetSize() const 
	{
		return m_nSize;
	}
	int GetUpperBound() const;
	void SetSize(__int64 nNewSize, __int64 nGrowBy = -1);
	void SetMatixSize(__int64 nNewXSize, __int64 nNewYSize, __int64 nGrowBy = -1);

// Operations
	// Clean up
	void FreeExtra();
	void RemoveAll();

	// Accessing elements
	inline double GetAt(__int64 nIndex) const 
		{ 
			ASSERT(nIndex >= 0 && nIndex < m_nSize);
			double val = m_pData[nIndex];
			return (!pNTesting->IsNaNorInfinity(val) ? val : 0.0);
	}
	inline void SetAt(__int64 nIndex, double newElement) 
	{ 
		ASSERT(nIndex >= 0 && nIndex < m_nSize); 
	    if(!pNTesting->IsNaNorInfinity(newElement))
			m_pData[nIndex] = newElement;
		else
			m_pData[nIndex] = 0.0;
	}
	inline double& ElementAt(__int64 nIndex) 
	{
		static double zero = 0.0;
		ASSERT(nIndex >=0 && nIndex< m_nSize); 
		static double val = m_pData[nIndex];
		return (!pNTesting->IsNaNorInfinity(val)) ? val : zero;
	}
	void Empty();

	// Potentially growing the array
	void SetAtGrow(__int64 nIndex, double newElement);
	__int64 Add(double newElement) 
	{
		__int64 nIndex = m_nSize; 
		if(!pNTesting->IsNaNorInfinity(newElement))
			SetAtGrow(nIndex,newElement);
		else
			SetAtGrow(nIndex,0.0);
		return nIndex;
	}

	// overloaded operator helpers
	virtual inline double operator[](__int64 nIndex) const 
	{
		return GetAt(nIndex);
	}
	virtual inline double& operator[](__int64 nIndex)	
	{
		return m_pData[nIndex];
	}
	virtual const CDoubleArray& operator = (const CDoubleArray& sData);

	// Operations that move elements around
	void InsertAt(__int64 nIndex, double newElement, __int64 nCount = 1);
	void RemoveAt(__int64 nIndex, __int64 nCount = 1);
	void InsertAt(__int64 nStartIndex, CDoubleArray* pNewArray);

	// Matrix operation
	void SetAtMatrix(__int64 posx, __int64 posy,double Value);
	double GetAtMatrix(__int64 posx, __int64 posy);
	inline __int64 GetSizeX() const 
	{
		return SizeX;
	}
	inline __int64 GetSizeY() const 
	{
		return SizeY;
	}

	// Expand operation
	bool CDoubleArray::ExpandTo(__int64 xchannels);
	bool CDoubleArray::ExpandTo(__int64 xchannels, __int64 ychannels);


protected:
	void AssignCopy(__int64 nSrcLen, double *Data);

// Implementation
public:
	double* m_pData;		// the actual array of data
	bool m_LoadError;
	
protected:
	__int32	m_VersionNumber;
	__int64 m_nSize;		// # of elements (upperBound - 1)
	__int64 m_nMaxSize;		// max allocated
	__int64 m_nGrowBy;		// grow amount

	__int64 SizeX;			// Size of Matrix in X
	__int64 SizeY;			// Size of Matrix in Y
	
	__int32 m_CompressionType;
	CNumberTesting *pNTesting;

public:
	~CDoubleArray();
	virtual void Serialize(CArchive& ar);

	void Dump(CDumpContext&) const;
	void AssertValid() const;
};

/////////////////////////////////////////////////////////////////////////////
// helper class CCodeInformation for CSourceCodeInformation
class COBOLDUTILITIES_APP CCodeInformation : public CObject
{
protected:
	CString	csCodeID;
	CString	csCodeType;
	CString	csCodeFileName;

public:
	// constructor and destructor
	CCodeInformation();
	CCodeInformation(CString CodeType, CString CodeID, CString CodeFileName);
	~CCodeInformation();

public:
	// implementation
	CString &GetType();
	CString &GetID();
	CString &GetFileName();
};

/////////////////////////////////////////////////////////////////////////////
// class to handle source code information of dlls
class COBOLDUTILITIES_APP CSourceCodeInformation
{
public:
	CObArray		coaCodeInformation;
	CString			csSourceCode;

public:
	// constructor and destructor
	CSourceCodeInformation();
	~CSourceCodeInformation();

public:
	// implementation
	INT_PTR GetCount();
	CString &GetSourceCode(CString csDllFilePathName, CString csSourceID, CString csSourceType);

	CString &GetTypeAt(unsigned __int32 ui32Index);
	CString &GetIDAt(unsigned __int32 ui32Index);
	CString &GetFileNameAt(unsigned __int32 ui32Index);
};

/////////////////////////////////////////////////////////////////////////////
// definition for exported functions
class CCoboldApp;
class CMainFrame;
class CCoboldDoc;

/////////////////////////////////////////////////////////////////////////////
// definition for exported functions

COBOLDUTILITIES_APP __int32 CheckDate(CString Module);

COBOLDUTILITIES_APP COLORREF GetTNGColor(CDC *pDC, __int32 ColorIndex);
COBOLDUTILITIES_APP COLORREF GetTNGScreenColor(__int32 ColorIndex);
COBOLDUTILITIES_APP COLORREF GetTNGPrintColor(__int32 ColorIndex);
COBOLDUTILITIES_APP void GetTNGDefaultColors(void);
COBOLDUTILITIES_APP void SetTNGScreenColor(__int32 ColorIndex, COLORREF Color);
COBOLDUTILITIES_APP void SetTNGPrintColor(__int32 ColorIndex, COLORREF Color);
COBOLDUTILITIES_APP void TogglePrintScreenColors(void);
COBOLDUTILITIES_APP void ReadColorDefinitions(void);
COBOLDUTILITIES_APP void ReadDelimiterDefinitions(void *pvView);
COBOLDUTILITIES_APP void WriteColorDefinitions(void);
COBOLDUTILITIES_APP void WriteDelimiterDefinitions(void *pvView);
COBOLDUTILITIES_APP CString Int64ToDelimitedCString(CString format, __int64 i64Value);
COBOLDUTILITIES_APP CString DoubleToDelimitedCString(double dValue);

// Conversion functions
COBOLDUTILITIES_APP double GetCStringNumber(CString cAddress);
COBOLDUTILITIES_APP void DoubleAtari(double register *var);
COBOLDUTILITIES_APP void LongAtari(unsigned long register *var);
COBOLDUTILITIES_APP void IntAtari(unsigned short register *var);
/// Conversions end

// myTime functions
extern COBOLDUTILITIES_APP dllGetTickCounts64 fGetTickCount64;
COBOLDUTILITIES_APP void ToAtariTime(CTime *pCTime, ADateTime *pATime);
COBOLDUTILITIES_APP void ToCTime(CTime *pCTime, ADateTime *pATime);
COBOLDUTILITIES_APP bool InitTickCount64Function();
/// myTime end

// PumpMessages functions
COBOLDUTILITIES_APP void PumpDlgMessages(CWnd *pWnd);
COBOLDUTILITIES_APP void PumpDlgMessagesNoIdle(CWnd *pWnd);
COBOLDUTILITIES_APP void PumpMessages(bool bIdle=true);
COBOLDUTILITIES_APP void PumpMessagesNoIdle();
/// PumpMessage end

COBOLDUTILITIES_APP bool ReadWindowPlacement(WINDOWPLACEMENT *pwp, UINT *puiFlags, char *pszSection, char *pszWindowFlag, char *pszWindowPos);
COBOLDUTILITIES_APP void WriteWindowPlacement(CWnd *pWnd, char *pszSection, char *pszWindowFlag, char *pszWindowPos);
COBOLDUTILITIES_APP bool TestFlatBarAvailable(void);

COBOLDUTILITIES_APP __int32 GetTaskListNT(PTASK_LIST  pTask, DWORD dwNumTasks);
COBOLDUTILITIES_APP BOOL CALLBACK EnumWindowsProc(HWND hwnd, LPARAM lParam);
COBOLDUTILITIES_APP __int32 CountApplications(CString VersionFileDescription);

COBOLDUTILITIES_APP __int32 FileNotFoundMessage(CStringArray *pActiveBatchFile, CString BatchName, bool bQuitMessage = false);

COBOLDUTILITIES_APP HRESULT GetComCtlVersion(LPDWORD pdwMajor, LPDWORD pdwMinor);

COBOLDUTILITIES_APP void DeleteLocalRegistryKey(HKEY myKey, char RegPath[MAX_PATH]);

COBOLDUTILITIES_APP void CorrectGP1DifferentialNonlinearity(CDoubleArray &EventData, CDoubleArray &Parameters, __int32 rawdata, __int32 iRes);

// Application functions
COBOLDUTILITIES_APP CString &GetApplicationPath();
COBOLDUTILITIES_APP CCoboldApp *GetCoboldApp();
/// Application end

COBOLDUTILITIES_APP CString GetSerialNumber();
COBOLDUTILITIES_APP __int32 GetSerialNumberKey();
COBOLDUTILITIES_APP bool IsSerialNumberOK();
COBOLDUTILITIES_APP bool IsSerialNumberHM1();
COBOLDUTILITIES_APP bool IsSerialNumberDemo();
COBOLDUTILITIES_APP bool IsDemoExpired(bool flag = false);
COBOLDUTILITIES_APP void maInit();

COBOLDUTILITIES_APP void OrthogonalToRPhi(double x,double y,double &r,double &phi);

COBOLDUTILITIES_APP void SetActualDAqPathName(CString csPathName);
COBOLDUTILITIES_APP void SetActualDAnPathName(CString csPathName);
COBOLDUTILITIES_APP void SetActualFCPathName(CString csPathName);
COBOLDUTILITIES_APP CString& GetActualDAqPathName();
COBOLDUTILITIES_APP CString& GetActualDAnPathName();
COBOLDUTILITIES_APP CString& GetActualFCPathName();

COBOLDUTILITIES_APP bool IsCoboldExecutingCommand();
COBOLDUTILITIES_APP void ExecuteCommand(CString csCommandLine);
COBOLDUTILITIES_APP CDoubleArray &GetDAqDAnParameters(CCoboldDoc *pDoc = nullptr);
COBOLDUTILITIES_APP CDoubleArray &GetDAqDAnWeighParameters(CCoboldDoc *pDoc = nullptr);
COBOLDUTILITIES_APP CDoubleArray &GetDAqDAnEventData(CCoboldDoc *pDoc = nullptr);
COBOLDUTILITIES_APP CCoboldDoc *GetDocumentPointer();

COBOLDUTILITIES_APP bool IsClearEventDataArraySet();
COBOLDUTILITIES_APP void SetClearEventDataArrayState(bool flag);

COBOLDUTILITIES_APP bool AreCompressCOMsAvailable(bool bInfoBox);

COBOLDUTILITIES_APP void DisplayLastError(LPTSTR lpszFunction);

COBOLDUTILITIES_APP bool IsWindows64();
COBOLDUTILITIES_APP bool IsProcess64();
COBOLDUTILITIES_APP bool IsVistaOrHigher();
COBOLDUTILITIES_APP bool ErrorMessageRunningOnX64OS(CString infoText);

COBOLDUTILITIES_APP CString& GetHID(CString csFilePath);
COBOLDUTILITIES_APP BOOL UpdateHID(CString csFilePath);

// Path functions
COBOLDUTILITIES_APP inline BOOL IsDirectorySeparator(TCHAR ch);
/// Path end

// LMF functions
COBOLDUTILITIES_APP bool IsLMFIdle();
COBOLDUTILITIES_APP bool IsDAqTerminating();
COBOLDUTILITIES_APP bool ProcessDAqFlushing(CArchive *pAr);
COBOLDUTILITIES_APP void SetInitialFlushTime(CTimeSpan ctsFlushTimeDelta);
COBOLDUTILITIES_APP CTimeSpan& GetInitialFlushTime();

// DAnDAqWizard
COBOLDUTILITIES_APP BOOL DAnDAqWizardShowForm();

// Config
extern COBOLDUTILITIES_APP void *pxmlProfile;
COBOLDUTILITIES_APP void *GetActualXMLProfile();

// RoundUtilities
COBOLDUTILITIES_APP __int32 RoundToNearestInt32(double dInput);
COBOLDUTILITIES_APP unsigned __int32 RoundToNearestUInt32(double dInput);
COBOLDUTILITIES_APP __int64 RoundToNearestInt64(double dInput);
COBOLDUTILITIES_APP unsigned __int64 RoundToNearestUInt64(double dInput);

// Strings
COBOLDUTILITIES_APP __int32 FindCharNotInQuotes(CString csString, char quoteCharacter, char searchCharacter);

// ThreadName
COBOLDUTILITIES_APP void SetThreadName( DWORD dwThreadID, const char* threadName);

// GetTextBoundingRect
COBOLDUTILITIES_APP BOOL GetTextBoundingRect(HDC hDC, int x, int y, CString csStr, CRect &rect);  // Holds bounding rectangle

// CoboldCommand
COBOLDUTILITIES_APP bool SendCoboldCommand(CString CommandLine);

//#ifdef __cplusplus
//}
//#endif

/////////////////////////////////////////////////////////////////////////////

#endif
