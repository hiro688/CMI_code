// CDAn.cpp : User-Stuff routines for the DLL.
//

#include "stdafx.h"

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <float.h>

#include "UserSHM.h"
#include "CoboldParser.h"
#include "LMFPreEventData.h"
#include "CoboldUtilities.h"

#include "CDAn.h"
#include "DAnUtilities.h"

#include "CDAq.h"
#include "LMInfo.h"

#include "UserSP.h"

#ifdef _DEBUG
#define new DEBUG_NEW
#undef THIS_FILE
static char THIS_FILE[] = __FILE__;
#endif

/////////////////////////////////////////////////////////////////////////////
// insert the subprogram part for software insert here
// ------> update dependencies <------

////////////////////////////////////////
//
//  RoentDek Standard DAn
//
////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//	Standard User defined analysis part called from CoboldPC main program
//  (c) RoentDek Handels GmbH
//
//  V1 - 20.07.2001
//  V2 - 08.03.2002		- is now independent from # of Hits of DAq
//						- n = number of hit information now calculated
//  V3 - 08.04.2002		- adaption to new layout for DAn (hex anode)
//  V4 - 13.05.2002     - hex anode code adjustments
//  V4.1 - 24.05.2002	- subversion to 1
//						- Parameter 106 behavior corrected when "not automatic"
//						- test for sufficient # of coordinates defined
//  V4.2 - 01.09.2005	- Xvw calculation corrected (1/sqrt(3.) * - eliminated)
//  V4.3..V5.5			- No changes
//  V5.5 - 09.09.2005   - HM1 ABM mode implemented
//  V5.6 - 14.11.2005	- 2HM1 StartOfDAnData corrected
//  V5.7 - 31.01.2006	- Corrected Hex calculations
//						- Support for TDC8HP
//						- time stamp for LM_CAMAC and LM_LONG implemented
//  V5.8 - 18.07.2006	- fixed problem with function DAnGetLastLMFName()
//  V5.9 - 23.08.2006	- fixed problem for 2TDC8 Modules detecting DAn start coordinates
//						- fixed problem with Parameter 2 != 2
//  V5.10 - 28.08.2006  - fixed problem with HM1-ABM Mode
//  V5.11 - 31.08.2006  - sums and differences modified
//								sums and differences in channels if conversion set to channel
//								sums and differences in ns (TIME) if conversion set to other than channel
//  V5.12 - 06.03.2007  - Parameter 125 added
//  V5.13 - 22.03.2007  - Parameter 140 added
//  V5.14 - 19.08.2007  - Support for UserDefined Data defined and partially supported
//						- Restart i32StartDAqTDCData problem corrected
//  V6.00 - 01.09.2007	- Moved to Version 6 of DAn
//	V6.01 - 18.07.2008	- Changes made to newly USER_DEF Format for HPTDC8, HM1, TDC8, TDC8PCI
//  V6.02 - 05.11.2008	- Added Coordinates for False,Const1,Const2,Const3,Const4,Const5,Const6,Const7,Const8
//  V6.03 - 23.11.2008	- Modified to new EventData Transfer (preEventData)
//  V7.00 - 27.05.2009	- included MaskSimulation, RateAveragingClass, ReflectionCoordinates
//  V7.01 - 09.10.2009  - Minor corrections by Achim
//  V10.00 - 03.03.2011 - Changed Version and reset subversion
//						- CheckID changed... and modified. Separated IDs for DAn and DAq
//						- new Parameter 1050 for DAn CheckID
//						- RoentDek DAn modules parameter now stating with 1000
//						- indices for EventData, Parameter and WeighParameter now starting from 0 NOT from 1
//	V10.01 - 30.11.2011 - value of -1.200 changed to -1.e200;
//  V10.02 - 31.01.2012 - Modifications in DAn start coordinate calculation to match new HM1 DAq module
//	V10.03 - 01.10.2012	- srand init with 0
//  V10.04 - 15.11.2013 - TOF_ns always in ns (independent from conversion parameter)
//						- reflection_in_MCP coordinate now calculating Hit2-Hit1 in case Parameter 1025 = 0, other than 0 no change in behavior
//	V10.05 - 05.06.2014 - modified Parameter 1002 to support HEX-DAN Message if set
//  V10.06 - 02.08.2014	- use Constx from 1-i32NumberOfChannels
//						- test needed coordinates accordingly
//	V10.07 - 24.10-2ß14 - reflection_in_MCP coordinate now calculating Hit2-Hit1 TDC changed from channel 0 to channel 8 in case Parameter 1025 = 0, other than 0 no change in behavior
///////////////////////////////////////////////////////////////////////////

#define CHECKID_DANCCF	201102080000

#define DAQ_VERSION10	20110208		// 08.02.2011
#define DAQ_VERSION7	20080507		// 07.05.2008
#define DAQ_VERSION6	20080901
#define DAQ_VERSION5	20020408
#define DAQ_VERSION4	20020408

#define LMF_VERSION10	0x000a
#define LMF_VERSION5	5
#define LMF_VERSION6	6
#define LMF_VERSION7	7
#define LMF_VERSION8	8

#define DAN_VERSION10	20110208		// 08.02.2011
#define DAN_VERSION7	20090527
#define DAN_VERSION6	20070901
#define DAN_VERSION5	20020513

#define DAN_SUBVERSION	0x0007		// increase with 1 (start with 0 at V6)

/////////////////////////////////////////////////////////////////////////////
// Parameter description used in this insert dependent part!
// ---------------------------------------------------------
//
// Used from DAq
// -------------
// Parameter  2 = Save TimeStamp
//                0 = no Timestamp,
//                1 = 32Bit Timestamp	(Low.Low, Low.high)
//                2 = 64Bit Timestamp	(Low.Low, Low.high, High.Low, High.high)
// Parameter  5 = TimeScaling (Internally set, tics per second)
// Parameter  6 = DAq Version # (Internally set)
// Parameter  7 = Time Reference of DAq Initialize (Start time of LMF) (Internally set)
// Parameter  8 = DAQ_ID
//					DAQ_ID_RAW			0x000000		// for RAW (no Data)
//					DAQ_ID_HM1			0x000001		// for HM1 (single)
//					DAQ_ID_TDC8			0x000002		// for TDC8/ISA/PCI
//					DAQ_ID_CAMAC		0x000003		// for CAMAC
//					DAQ_ID_2HM1			0x000004		// for 2 HM1
//					DAQ_ID_2TDC8		0x000005		// for 2 TDC8
//					DAQ_ID_HM1_ABM		0x000006		// for HM1 ABM Mode
//					DAQ_ID_HM1_LR		0x000007		// for HM1 LR Mode
//					DAQ_ID_HPTDC		0x000008		// for TDC8HP
//					DAQ_ID_TCPIP		0x000009		// for TCPIP (not supported yet)
//					DAQ_ID_HPTDCRAW		0x000010		// for TDC8HP writing RAW data
//
// Parameter 20 = Resolution of TDC in ns (internally set)
// Parameter 21 = TDC data type information (internally set)
//			0 = Not defined
//			1 = Channel information
//			2 = Time information (in ns)
//
// Parameter 32 = number of Channels (reread during offline)
//				1..
// Parameter 33 = number of hits (reread during offline)
//              1..
//
// Parameter 40 = DataFormat (Internally set)
// Parameter 82 and 83 for 2HM1 Mode
//
// Needed by DAn
// -------------
// Parameter 1000 = Conversion Parameter for RAW data
//			0 = TDC bins (no conversion)
//			1 = Time (ns)
//			2 = Point (mm)
// Parameter 1002 = DLD/Hex-Anode calculations
//			0 = DLD-Anode
//			1 = Hex-Anode	(information displayed)
//			2 = Hex-Anode	(no information displayed)
// Parameter 1003 = PHI conversion
//			0 = RAD [-pi..pi]
//			1 = RAD [0..2pi]
//			2 = DEG [-180..180]
//			3 = DEG [0..360]
// Parameter 1004 = DNL correction (GP1/HM1 only)
//			0 = no DNL correction
//			1 = Correction value (typically 0.31)
// Parameter 1005 = Start of DAq Data for DAn (Start Coordinate)
//			-1 = automatic
// Parameter 1006 = Start of DAn Data (Start Coordinate)
//			-1 = automatic
// Parameter 1007 = Analyze hit #
//
// Parameter 1010 = pTPCalX = Time to Point calibration factor for x (mm/ns)
// Parameter 1011 = pTPCalY = Time to Point calibration factor for y (mm/ns)
// Parameter 1012 = pTPCalZ = Time to Point calibration factor for z (mm/ns)

// Parameter 1013 to 1018 = binning information for histograms

// Parameter 1020 = pCOx = Rotation Offset Center for x
// Parameter 1021 = pCOy = Rotation Offset Center for y
// Parameter 1022 = pRotA = Rotation Angle mathematical direction
// 		      		value in RAD if Parameter 1003 = 0 or 1
//		      		value in DEG if Parameter 1003 = 2 or 3
// Parameter 1023 = PosX-value of center for r/phi coordinates
// Parameter 1024 = PosY-value of center for r/phi coordinates
//
// Parameter 1025 = MCP channel for sum calcualtion sum = x1+x2-2*mcp, or sum = x1+x2 for para 1025 = -1
// Parameter 1026 = channel number for x1
// Parameter 1027 = channel number for x2
// Parameter 1028 = channel number for y1
// Parameter 1029 = channel number for y2
// Parameter 1030 = channel number for z1 (ignored if parameter 1002 = 0)
// Parameter 1031 = channel number for z2 (ignored if parameter 1002 = 0)
// Parameter 1032 = channel number for TOF (0 if not used)


// Parameter 1035 = pOPx = Offset for x Point
// Parameter 1036 = pOPy = Offset for y Point
// Parameter 1037 = pOPw = Offset for w Point
// Parameter 1038 = pOSum = Offset for Sum/Diff calculations

// Parameter 1039 = AntiMoire (1 = yes, 0 = no)

// Parameter 1040 = dEventCounterReset
//			0 = no reset
//			1 = reset
//			tested in AnalysisProcessEvent
//			tested in AnalysisInitialize
//
// Parameter 1041 = rate integration time in seconds (default = 1)
// Parameter 1050 = check number to test DAn and CCF for compatibility
// Parameter 1060 = condition flag 1
//
//
////////////////////////////////////////////////////////////////////////////
// Conversions
/////////////////////////////////////////////////////////////////////////////
// to time
//	time = TDCR / channel					(ns)
//		TDCR = TDCResolution from DAq Parameter 
//  point = time / pTPCal
//		pTPCal = time (ns)/mm
// ROT = (cos   -sin)
//		 (sin   -cos)

/////////////////////////////////////////////////////////////////////////////
// global definition of variables

LARGE_INTEGER	li32TimeStamp;	// TimeStamp time information
CTime ctLMFStartTime;		// Start Time of LMF

__int32 i32TimeStamp;		// parameter 2
double dTimeScaling;		// parameter 5 - Time Scaling (ticks per second)

__int32 i32DAq_ID;			// parameter 8

double dTDCResolution;		// parameter 20
__int32 i32TDCDataType;		// parameter 21

__int32	i32NumberOfChannels;// parameter 32
__int32	i32NumberOfHits;	// parameter 33
__int32 i32DataFormat;		// parameter 40

__int32 i32Conversion;		// parameter 1000
__int32 i32HexAnode;		// parameter 1002
__int32 i32PhiConversion;	// parameter 1003
double dDnlCorrection;		// parameter 1004
__int32 i32StartDAqData;	// parameter 1005
__int32 i32StartDAnData;	// parameter 1006
__int32 i32UseHit;			// parameter 1007

double dTPCalX;				// parameter 1010
double dTPCalY;				// parameter 1011
double dTPCalZ;				// parameter 1012

double dCOx;				// parameter 1020
double dCOy;				// parameter 1021
double dRotA;				// parameter 1022

double dCRPhix;				// parameter 1023
double dCRPhiy;				// parameter 1024

__int32 i32Cmcp;			// parameter 1025
__int32 i32Cx1,i32Cx2;		// parameter 1026 to 1031
__int32 i32Cy1,i32Cy2;
__int32 i32Cz1,i32Cz2;

__int32 i32TOFChannel;		// parameter 1032

double dOPx;				// parameter 1035
double dOPy;				// parameter 1036
double dOPw;				// parameter 1037
double dOSum;				// parameter 1038
bool	bAntiMoire;			// parameter 1039

__int32 i32StartDAqTDCData;

double dEventCounter = 0;	// dEventCounter for the data in LM-file

RateAveragingClass *racpRateAveragingInstance;

/////////////////////////////////////////////////////////////////////////////
// MFM info variables
bool bIsMFM = false;							// flag for indicating MFM
bool bFirstFile = false;						// flag for indicating first file in MFM
bool bLastFile = false;							// flag for indicating last file in MFM

///////////////////////////////
// externals
extern CUserSpectrum *pDAnUserSP;

///////////////////////////////
// externals via dllimport
__declspec(dllimport) __int32 DAqTimeStamp;

///////////////////////////////
// function declarations
double GetReflectionValue(__int32 C1,__int32 C2, __int32 counts[], CDoubleArray &EventData);

///////////////////////////////
// in lines
inline __int32 signofd(double a)
{ 
	return (a == 0.0) ? 0 : (a<0.0 ? -1 : 1); 
}

///////////////////////////////
// AnalysisGetInformationString
///////////////////////////////
// is called during startup procedure of CoboldPC
// 
// return value is a string that will be displayed in 
// the splash box and the about box

CString myInfoString;
CDAN_API LPCTSTR AnalysisGetInformationString()
{
	CString DAnDebugInfo;
#ifdef _DEBUG
	DAnDebugInfo = "D";
#endif
	myInfoString.Format("Standard Analysis(%sV %08d - %04d, %04d)",DAnDebugInfo,DAN_VERSION10,DAN_SUBVERSION,LMF_VERSION10);

	return LPCTSTR(myInfoString);
}

/////////////////////
// AnalysisInitialize
/////////////////////
// is called when new command is executed
//
// return value is false -> error during initialize
//                 true  -> initialize ok 

CDAN_API BOOL AnalysisInitialize(CDoubleArray &EventData,CDoubleArray &Parameter, CDoubleArray &WeighParameter)
{
	// initialize the random generator
	//srand( (unsigned __int32)time( nullptr ) );			// random seed
	srand(0);												// fixed seed

	__int32 DAqloops = RoundToNearestInt32(Parameter[53]);

	if(!DAqloops) 
	{
		AfxMessageBox("No data will be read from TDC because parameter 53 is set to zero");
		return false;
	}

	if(!pDAnUserSP) 
		pDAnUserSP = (CUserSpectrum *)new CUserSpectrum();

	int iFileNum;
	CString csPathName, csBasePathName;
	int iStart, iEnd;

	bool ret = pDAnUserSP->GetMultiFileInformation(iFileNum,csPathName,csBasePathName,iStart,iEnd,bFirstFile,bLastFile);

	_dOldEventTime = 0.0;
	_dStartEventTime = 0.0;

	// first check if all parameters are set
	if(Parameter.GetSize() < 1060)
	{
		// indicate parameter number error
		__int32 iAnswer = AfxMessageBox("Not all parameters are defined\n for this DAn module!\n\nYou may ignore this on your own risk!\n\nTo Ignore press YES",MB_ICONQUESTION|MB_YESNO);
		if(iAnswer == IDNO)
			return false;
	}

	// check DAq-Version
	unsigned __int32 _ui32DAqVersion = RoundToNearestUInt32(Parameter[6]);
	if((_ui32DAqVersion != DAQ_VERSION5) && (_ui32DAqVersion != DAQ_VERSION6) && (_ui32DAqVersion != DAQ_VERSION7) && (_ui32DAqVersion != DAQ_VERSION10))
	{
		// indicate DAq version error
		CString MsgText;
		MsgText.Format("DAn module works only with list mode data\ntaken with Standard DAq-Modules version\n(%d, %d, %d and %d)!",
			DAQ_VERSION5, DAQ_VERSION6, DAQ_VERSION7, DAQ_VERSION10);
		MsgText += "\n\nYou may ignore this on your own risk!\n\nTo Ignore press YES";
		__int32 i32Answer = AfxMessageBox(MsgText,MB_ICONQUESTION|MB_YESNO);
		if(i32Answer == IDNO)
			return false;
	}

	if(RoundToNearestUInt64(Parameter[1050]) != CHECKID_DANCCF) 
	{
		AfxMessageBox(CString("Parameter 1050 indicates that the CCF\n") + 
			CString("and DAn are not compatible\n"));
		return 0;
	}

	// transfer parameters
	//    in the next lines you'll find the following correction values
	//    0.1 for float to int conversion
	//    -1 if parameter is for indexing
	i32TimeStamp = RoundToNearestInt32(Parameter[2]);								// parameter 2
	dTimeScaling = Parameter[5];													// parameter 5
	ctLMFStartTime = CTime((time_t)(RoundToNearestInt32(Parameter[7])));			// parameter 7
	i32DAq_ID = RoundToNearestInt32(Parameter[8]);									// parameter 8

	dTDCResolution = Parameter[20];													// parameter 20

	i32TDCDataType = RoundToNearestInt32(Parameter[21]);							// parameter 21

	i32NumberOfChannels = RoundToNearestInt32(Parameter[32]);						// parameter 32
	i32NumberOfHits = RoundToNearestInt32(Parameter[33]);							// parameter 33
	i32DataFormat = RoundToNearestInt32(signofd(Parameter[40]+0.1)<0 ? Parameter[40]-0.1 : Parameter[40]+0.1);	// parameter 40	

	i32Conversion = RoundToNearestInt32(Parameter[1000]);							// parameter 1000
	i32HexAnode = RoundToNearestInt32(Parameter[1002]);								// parameter 1002
	i32PhiConversion = RoundToNearestInt32(Parameter[1003]);						// parameter 1003
	dDnlCorrection = Parameter[1004];												// parameter 1004
	i32StartDAqData = RoundToNearestInt32(Parameter[1005]);							// parameter 1005
	i32StartDAnData = RoundToNearestInt32(Parameter[1006]);							// parameter 1006
	i32UseHit = RoundToNearestInt32(Parameter[1007]);								// parameter 1007

	dTPCalX = Parameter[1010];														// parameter 1010
	dTPCalY = Parameter[1011];														// parameter 1011
	dTPCalZ = Parameter[1012];														// parameter 1012

	dCOx = Parameter[1020];															// parameter 1020
	dCOy = Parameter[1021];															// parameter 1021
	dRotA = Parameter[1022];														// parameter 1022

	dCRPhix =  Parameter[1023];														// parameter 1023
	dCRPhiy =  Parameter[1024];														// parameter 1024

	i32Cmcp = RoundToNearestInt32(Parameter[1025])-1;								// parameter 1025
	i32Cx1 = RoundToNearestInt32(Parameter[1026])-1;								// parameter 1026
	i32Cx2 = RoundToNearestInt32(Parameter[1027])-1;								// parameter 1027
	i32Cy1 = RoundToNearestInt32(Parameter[1028])-1;								// parameter 1028
	i32Cy2 = RoundToNearestInt32(Parameter[1029])-1;								// parameter 1029
	i32Cz1 = RoundToNearestInt32(Parameter[1030])-1;								// parameter 1030
	i32Cz2 = RoundToNearestInt32(Parameter[1031])-1;								// parameter 1031
	i32TOFChannel = RoundToNearestInt32(Parameter[1032])-1;							// parameter 1032

	dOPx = Parameter[1035];															// parameter 1035
	dOPy = Parameter[1036];															// parameter 1036
	dOPw = Parameter[1037];															// parameter 1037
	dOSum = Parameter[1038];														// parameter 1038
	bAntiMoire = RoundToNearestInt32(Parameter[1039]) ? true : false;				// parameter 1039
	bool bdEventCounterReset = RoundToNearestInt32(Parameter[1040]) ? true : false;	// parameter 1040

	// check parameter 20 for valid data
	if(Parameter[20] <= 0.0)
	{
		// indicate TDC resolution error
		__int32 i32Answer = AfxMessageBox("Parameter 20\nTDC-resolution\ncontains no valid data!\n\nValues should be >= 0.0\n\nYou may ignore this on your own risk!\n\nTo Ignore press YES",MB_ICONQUESTION|MB_YESNO);
		if(i32Answer == IDNO)
			return false;
	}

	// check parameter 21 for valid data
	if(RoundToNearestInt32(Parameter[21]) < 0 || RoundToNearestInt32(Parameter[21]) > 2)
	{
		// indicate TDC-data type error
		__int32 i32Answer = AfxMessageBox("Parameter 21\nTDC-data type\ncontains no valid data!\n\nValues should be 0,1 or 2\n\nYou may ignore this on your own risk!\n\nTo Ignore press YES",MB_ICONQUESTION|MB_YESNO);
		if(i32Answer == IDNO)
			return false;
	}

	// check parameter 1002 for valid data
	if((i32HexAnode < 0) || (i32HexAnode > 2))
	{
		__int32 i32Answer = AfxMessageBox("Parameter 1002\nHexAnode\ncontains no valid data!\n\nValues should be [0..2]\n\nYou may ignore this on your own risk!\n\nTo Ignore press YES (assuming HexAnode)",MB_ICONSTOP|MB_YESNO);
		if(i32Answer == IDNO)
			return false;
	}
	if(i32HexAnode == 1)
	{
		__int32 i32Answer = AfxMessageBox("Please note that there is a special\nversion of the data analysis available\nfor HEX-detectors.\nPlease contact RoentDek.\n\nIf you want to continue with the (limited) standard version\nthen please set parameter 1002 to 2\n\nTo Ignore press YES (assuming HexAnode)",MB_ICONEXCLAMATION|MB_YESNO);
		if(i32Answer == IDNO)
			return false;
	}

	// set dEventCounter to zero at start of new command
	if(bdEventCounterReset)
	{
		dEventCounter = 0;
		Parameter[1040] = false;
	}

	// correct data for start of DAn coordinates
	// first the start of DAqData
	if(i32StartDAqData < 0)
	{
		i32StartDAqData = i32StartDAqTDCData = 0;
		Parameter[1005] = i32StartDAqTDCData;	// write information back to parameter 1005
	}

	// second the start of DAnData
	if(i32StartDAnData < 0)
	{
		if(i32DAq_ID == DAQ_ID_HM1_ABM) // correct ABM start DAn data for standard DAn
			i32StartDAnData = i32StartDAqTDCData + (i32NumberOfChannels * (i32NumberOfHits+1));
		else if(i32DAq_ID == DAQ_ID_2HM1)
		{
			__int32 ip2NumberOfChannels = RoundToNearestInt32(Parameter[82]);						// parameter 82
			__int32 ip2NumberOfHits = RoundToNearestInt32(Parameter[83]);							// parameter 83

			i32StartDAnData = i32StartDAqTDCData + (i32NumberOfChannels * (i32NumberOfHits+1));
			i32StartDAnData += (ip2NumberOfChannels * (ip2NumberOfHits+1));
		}
		else if(i32DAq_ID == DAQ_ID_2TDC8)
		{
			__int32 ip2NumberOfChannels = RoundToNearestInt32(Parameter[34]);						// parameter 34
			__int32 ip2NumberOfHits = RoundToNearestInt32(Parameter[35]);							// parameter 35

			i32StartDAnData = i32StartDAqTDCData + (i32NumberOfChannels * (i32NumberOfHits+1));
			i32StartDAnData += (ip2NumberOfChannels * (ip2NumberOfHits+1));
		}
		else
		{
			if(i32DAq_ID == DAQ_ID_CAMAC)
				i32StartDAnData = i32StartDAqTDCData + (i32NumberOfChannels * (i32NumberOfHits));
			else
				i32StartDAnData = i32StartDAqTDCData + (i32NumberOfChannels * (i32NumberOfHits+1));
		}
		i32StartDAnData += 1; // +1 for LowResLevelInfo of TDC8HP			

		Parameter[1006] = double(i32StartDAnData);			// write information back to parameter 1006
	}

	// test for sufficient # of coordinates defined
	if((EventData.GetSize() < i32StartDAnData + 56 + i32NumberOfChannels))
	{
		// indicate TDC-data type error
		__int32 i32Answer = AfxMessageBox("Not all coordinates are defined\nfor this DAn module!\n\n\nYou may ignore this on your own risk!\n\nTo Ignore press YES",MB_ICONQUESTION|MB_YESNO);
		if(i32Answer == IDNO)
			return false;
	}

	if(theDAnApp.SharedClassInstance) 
		theDAnApp.SharedClassInstance->bDAnIsRunning = true;

	if(racpRateAveragingInstance) 
	{
		delete racpRateAveragingInstance; 
		racpRateAveragingInstance = nullptr;
	}
	racpRateAveragingInstance = new RateAveragingClass();
	if(racpRateAveragingInstance) 
		racpRateAveragingInstance->dIntegrationTime = Parameter[1041];
	if(theDAnApp.SharedClassInstance) 
		if(theDAnApp.SharedClassInstance->bDAqIsRunningOnline && i32TimeStamp == 0) 
			racpRateAveragingInstance->StartThread();

	return true;
}

///////////////////////
// AnalysisProcessEvent
///////////////////////
// is called during event loop execution
//
CDAN_API __int32 AnalysisProcessEvent(CDoubleArray &EventData,CDoubleArray &Parameter, CDoubleArray &WeighParameter, LMFPreEventData &preEventData)
{
	double AbsoluteEventTime;			// ns since start
	double DeltaEventTime;				// This Time - PreviousTime
	double True = true;					// always true
	__int32 ConsistencyIndicator;
	__int32 PLLStatusLocked;			// totally locked then true else false

	__int32 counts[32];
	double x1,x2,y1,y2,z1,z2;
	double TOF_ns = 0.;
	double raw_x,raw_y,raw_w;
	double sumx,sumy,sumw, sumxyw, diffxy;
	double raw_sumx,raw_sumy,raw_sumw, raw_sumxyw, raw_diffxy;
	double PosX,PosY;
	double r,phi;
	double Xuv,Yuv,Xuw,Yuw,Xvw,Yvw;
	double dX,dY;

	//  Example of how to use spectrum commands
	//	pDAnUserSP->AddOneAt(2,20);			// add one in spectrum 2 at channel 20
	//	pDAnUserSP->AddValueAt(3,20,0.5);		// add 0.5 in spectrum 3 at channel 20

	memset(counts,0,32*sizeof(__int32));

	double dMCPChannelData = 0.;

	// get time information if present
	if(i32TimeStamp)
	{
		// AbsoluteEventTime
		AbsoluteEventTime = GetEventTime(preEventData,Parameter);
		// AbsoluteDeltaEventTime
		DeltaEventTime = GetDeltaEventTime(preEventData,Parameter);
		// dEventCounter
	}

	if(racpRateAveragingInstance) 
		if(theDAnApp.SharedClassInstance) 
		{
			racpRateAveragingInstance->ui32EventCounter += unsigned __int32(theDAnApp.SharedClassInstance->rate);
			if(i32TimeStamp) 
				racpRateAveragingInstance->CheckTimestamp(AbsoluteEventTime);
		}

	// dEventCounter
	bool bdEventCounterReset = RoundToNearestInt32(Parameter[1040]) ? true : false;		// parameter 1040
	if(bdEventCounterReset)
	{
		dEventCounter = 0;
		Parameter[1040] = false;
	}
	dEventCounter += 1;

	// Get Status Information
	if(i32DAq_ID == DAQ_ID_HM1_ABM)
	{
		counts[0] = counts[1] = counts[2]= 1;
		PLLStatusLocked = false;
	}
	else if((i32DAq_ID == DAQ_ID_HM1) || (i32DAq_ID == DAQ_ID_2HM1))
	{
		for (__int32 ch = 0; ch < 4 ; ++ch) 
		{
			counts[ch] = (RoundToNearestInt32(EventData[(i32StartDAqTDCData+ch*(i32NumberOfHits+1))]) & 0x0007) -1;
			counts[ch] = counts[ch] < 0 ?  0 : counts[ch]; // correct negative (missed) hit
		}

		PLLStatusLocked = (RoundToNearestInt32(EventData[(i32StartDAqTDCData+0*(i32NumberOfHits+1))]) & 0x0080) &
			(RoundToNearestInt32(EventData[(i32StartDAqTDCData+1*(i32NumberOfHits+1))]) & 0x0080) &
			(RoundToNearestInt32(EventData[(i32StartDAqTDCData+2*(i32NumberOfHits+1))]) & 0x0080) &
			(RoundToNearestInt32(EventData[(i32StartDAqTDCData+3*(i32NumberOfHits+1))]) & 0x0080);
		PLLStatusLocked = PLLStatusLocked ? true : false;

	}
	else if((i32DAq_ID == DAQ_ID_TDC8) || (i32DAq_ID == DAQ_ID_2TDC8 || (i32DAq_ID == DAQ_ID_HPTDC) || (i32DAq_ID == DAQ_ID_HPTDCRAW)))
	{
		for(__int32 ch = 0; ch < i32NumberOfChannels ; ++ch) 
			counts[ch] = RoundToNearestInt32(EventData[(i32StartDAqTDCData+ch*(i32NumberOfHits+1))]);

		PLLStatusLocked = false;
	}
	else	// for all other... this information is not valid
		PLLStatusLocked = false;

	// ConsistencyIndicator
	ConsistencyIndicator = 0;
	ConsistencyIndicator += counts[i32Cx1] > 0 ? 1 : 0;
	ConsistencyIndicator += counts[i32Cx2] > 0 ? 2 : 0;
	ConsistencyIndicator += counts[i32Cy1] > 0 ? 4 : 0;
	ConsistencyIndicator += counts[i32Cy2] > 0 ? 8 : 0;
	if(i32HexAnode) 
	{
		ConsistencyIndicator += counts[i32Cz1] > 0 ? 16 : 0;
		ConsistencyIndicator += counts[i32Cz2] > 0 ? 32 : 0;
	}

	// Get Raw-Data
	if(i32DAq_ID == DAQ_ID_HM1_ABM)
		x1 = x2 = y1 = y2 = z1 = z2 = 0;
	else
	{
		x1 = EventData[(i32StartDAqTDCData+i32Cx1*(i32NumberOfHits+1)+i32UseHit)];
		x2 = EventData[(i32StartDAqTDCData+i32Cx2*(i32NumberOfHits+1)+i32UseHit)];
		y1 = EventData[(i32StartDAqTDCData+i32Cy1*(i32NumberOfHits+1)+i32UseHit)];
		y2 = EventData[(i32StartDAqTDCData+i32Cy2*(i32NumberOfHits+1)+i32UseHit)];
		if(i32HexAnode)
		{
			z1 = EventData[(i32StartDAqTDCData+i32Cz1*(i32NumberOfHits+1)+i32UseHit)];
			z2 = EventData[(i32StartDAqTDCData+i32Cz2*(i32NumberOfHits+1)+i32UseHit)];
		} 
		else 
			z1 = z2 = 0.;

		if(i32TOFChannel >= 0) 
		{
			if(counts[i32TOFChannel] > 0 ) 
				TOF_ns = EventData[(i32StartDAqTDCData+i32TOFChannel*(i32NumberOfHits+1)+1)];
			else
				TOF_ns = 0.;
		}
		else
			TOF_ns = 0.;

		if(i32Cmcp != -1)
		{
			dMCPChannelData = EventData[(i32Cmcp*(i32NumberOfHits+1)+i32UseHit)];
			if (i32DAq_ID == DAQ_ID_HPTDC && Parameter[88] > 0.5)
				TOF_ns = dMCPChannelData;
			if (!(i32DAq_ID == DAQ_ID_HPTDC && Parameter[88] > 0.5)) 
			{
				x1 -= dMCPChannelData;
				x2 -= dMCPChannelData;
				y1 -= dMCPChannelData;
				y2 -= dMCPChannelData;
				if(i32HexAnode)
				{
					z1 -= dMCPChannelData;
					z2 -= dMCPChannelData;
				}
				else
					z1 = z2 = 0.;
			}
		}
	}

	// correct DNL if
	if((i32DAq_ID == DAQ_ID_HM1) && dDnlCorrection)
	{
		x1 = CorrectGP1NDL(x1,dDnlCorrection);
		x2 = CorrectGP1NDL(x2,dDnlCorrection);
		y1 = CorrectGP1NDL(y1,dDnlCorrection);
		y2 = CorrectGP1NDL(y2,dDnlCorrection);
	}

	if(bAntiMoire) 
	{
		x1 += Rnd()-0.5;
		x2 += Rnd()-0.5;
		y1 += Rnd()-0.5;
		y2 += Rnd()-0.5;
		if(i32HexAnode) 
		{
			z1 += Rnd()-0.5;
			z2 += Rnd()-0.5;
		}
		if(i32TOFChannel >= 0) 
			if(counts[i32TOFChannel] > 0 ) 
				TOF_ns += Rnd()-0.5;
	}

	// now get the "real" position
	if(i32DAq_ID == DAQ_ID_HM1_ABM)
	{
		raw_x = RoundToNearestInt32(EventData[(i32StartDAqTDCData+0)]);
		raw_y = RoundToNearestInt32(EventData[(i32StartDAqTDCData+1)]);
		raw_w = RoundToNearestInt32(EventData[(i32StartDAqTDCData+2)]);

		raw_sumx = raw_sumy = raw_sumw = raw_sumxyw = raw_diffxy = -1.e200;
	}
	else
	{
		raw_x = (x1 - x2);
		raw_y = (y1 - y2);
		raw_sumx = x1+x2;
		raw_sumy = y1+y2;
		raw_sumxyw = raw_sumx + raw_sumy;
		raw_diffxy = raw_sumx - raw_sumy;

		if(i32HexAnode) 
		{
			raw_w = (z1 - z2);
			raw_sumw = z1+z2;
			raw_sumxyw += raw_sumw;
		} 
		else 
		{
			raw_w    = -1.e200;
			raw_sumw = -1.e200;
		}
	}

	// do conversion ? then first to time (ns)
	if(i32Conversion)
	{
		x1 *= dTDCResolution;
		x2 *= dTDCResolution;
		y1 *= dTDCResolution;
		y2 *= dTDCResolution;
		dMCPChannelData *= dTDCResolution;
		if(i32HexAnode)
		{
			z1 *= dTDCResolution;
			z2 *= dTDCResolution;
		}
	}
	TOF_ns *= dTDCResolution;

	// sums and differences
	// sums and differences in channels if parameter 1000 set to "channel"
	// sums and differences in ns (TIME) if parameter 1000 set to other than "channel"
	sumx = (x1 + x2) + dOSum;
	sumy = (y1 + y2) + dOSum;
	if(i32HexAnode)
		sumw = (z1 + z2) + dOSum;
	else
		sumw = 0;
	if(i32HexAnode)
		sumxyw = (sumx + sumy + sumw) - (2*dOSum);		// only one OSum -> -(2*dOSum)!!!
	else
		sumxyw = (sumx + sumy) - dOSum;				// only one OSum -> -(dOSum)!!!
	diffxy = (sumx - sumy) + dOSum;

	// convert also to position? then to position (mm)
	if(i32Conversion == 2)
	{
		x1 *= dTPCalX;
		x2 *= dTPCalX;
		y1 *= dTPCalY;
		y2 *= dTPCalY;
		if(i32HexAnode)
		{
			z1 *= dTPCalZ;
			z2 *= dTPCalZ;
		}
	}

	if(i32HexAnode)
	{
		double x = (x1-x2)*0.5;
		double y = (y1-y2)*0.5;
		PosX = x + dOPx;
		PosY =  (x-2.*y)/sqrt(3.) + dOPy;
	}
	else
	{
		double x = (x1-x2)*0.5;
		double y = (y1-y2)*0.5;
		PosX = x + dOPx;
		PosY = y + dOPy;
	}

	// do rotation
	if(dRotA) 
	{
		double xRot,yRot;
		RotateXY(PosX, PosY, dRotA, i32PhiConversion, dCOx, dCOy, xRot, yRot);
		PosX = xRot;
		PosY = yRot;
	}

	// convert to r-phi
	OrthoToRPhi(PosX, PosY, i32PhiConversion, dCRPhix, dCRPhiy, r, phi);

	if(i32HexAnode)
	{
		double x = (x1-x2)*0.5;
		double y = (y1-y2)*0.5;
		double w = (z1-z2)*0.5 + dOPw;
		Xuv	=	x + dOPx;
		Yuv	=	(x - 2.*y)/sqrt(3.) + dOPy;
		Xuw	=	Xuv;
		Yuw	=	(2.*w-x)/sqrt(3.) + dOPy;
		Xvw	=	(y+w) + dOPx;
		Yvw	=	(w-y)/sqrt(3.) + dOPy;
		dX	=	Xuv - Xvw;
		dY	=	Yuv - Yvw;
	}
	else
		Xuv = Yuv = Xuw = Yuw = Xvw = Yvw = dX = dY = DBL_MAX;		// not hex anode -> set to DBL_MAX 

	/////////////////////////////////////
	// write all data back to coordinates
	/////////////////////////////////////
	__int32 address = 0;
	EventData[i32StartDAnData+address++] = AbsoluteEventTime;
	EventData[i32StartDAnData+address++] = DeltaEventTime;
	EventData[i32StartDAnData+address++] = dEventCounter;
	EventData[i32StartDAnData+address++] = True;
	EventData[i32StartDAnData+address++] = 0; // false
	EventData[i32StartDAnData+address++] = ConsistencyIndicator;
	EventData[i32StartDAnData+address++] = PLLStatusLocked;

	if(racpRateAveragingInstance)
		EventData[i32StartDAnData+address++] = racpRateAveragingInstance->ui32Rate;	// rate
	else
		EventData[i32StartDAnData+address++] = 0.; // rate

	EventData[i32StartDAnData+address++] = Parameter[1060];	// manually set Condition1

	for (__int32 ch = 0; ch<8; ++ch)						// hit counter of the first 9 channels
		EventData[i32StartDAnData+address++] = counts[ch];

	EventData[i32StartDAnData+address++] = x1;
	EventData[i32StartDAnData+address++] = x2;
	EventData[i32StartDAnData+address++] = y1;
	EventData[i32StartDAnData+address++] = y2;
	EventData[i32StartDAnData+address++] = z1;
	EventData[i32StartDAnData+address++] = z2;

	EventData[i32StartDAnData+address++] = TOF_ns;

	EventData[i32StartDAnData+address++] = raw_x;
	EventData[i32StartDAnData+address++] = raw_y;
	EventData[i32StartDAnData+address++] = raw_w;

	EventData[i32StartDAnData+address++] = raw_sumx;
	EventData[i32StartDAnData+address++] = raw_sumy;
	EventData[i32StartDAnData+address++] = raw_sumw;
	EventData[i32StartDAnData+address++] = raw_sumxyw;
	EventData[i32StartDAnData+address++] = raw_diffxy;

	EventData[i32StartDAnData+address++] = sumx;
	EventData[i32StartDAnData+address++] = sumy;
	EventData[i32StartDAnData+address++] = sumw;
	EventData[i32StartDAnData+address++] = sumxyw;

	EventData[i32StartDAnData+address++] = diffxy;

	EventData[i32StartDAnData+address++] = PosX;
	EventData[i32StartDAnData+address++] = PosY;

	EventData[i32StartDAnData+address++] = r;
	EventData[i32StartDAnData+address++] = phi;

	EventData[i32StartDAnData+address++] = Xuv;
	EventData[i32StartDAnData+address++] = Yuv;
	EventData[i32StartDAnData+address++] = Xuw;
	EventData[i32StartDAnData+address++] = Yuw;
	EventData[i32StartDAnData+address++] = Xvw;
	EventData[i32StartDAnData+address++] = Yvw;

	EventData[i32StartDAnData+address++] = dX;
	EventData[i32StartDAnData+address++] = dY;

	double dMcpSignalDiff = -1.e200;
	if(i32NumberOfHits > 1)
	{
		if(i32Cmcp > -1)
		{
			if(counts[i32Cmcp] > 1) 
			{
				dMcpSignalDiff = EventData[(i32StartDAqTDCData+i32Cmcp*(i32NumberOfHits+1)+2)] - EventData[(i32StartDAqTDCData+i32Cmcp*(i32NumberOfHits+1)+1)];
				dMcpSignalDiff *= dTDCResolution;
			}
		}
		else if(i32Cmcp == -1)
		{	// if Parameter 1025 is set to 0 then perform the calculations for Hit2-Hit1 on TDC Channel 8 (normally x1)
			__int32 _i32Cmcp = 7;
			if(counts[_i32Cmcp] > 1) 
			{
				dMcpSignalDiff = EventData[(i32StartDAqTDCData+_i32Cmcp*(i32NumberOfHits+1)+2)] - EventData[(i32StartDAqTDCData+_i32Cmcp*(i32NumberOfHits+1)+1)];
				dMcpSignalDiff *= dTDCResolution;
			}
		}
	}
	EventData[i32StartDAnData+address++] = dMcpSignalDiff;

	EventData[i32StartDAnData+address++] = GetReflectionValue(i32Cx1,i32Cx2,counts, EventData);
	EventData[i32StartDAnData+address++] = GetReflectionValue(i32Cx2,i32Cx1,counts, EventData);
	EventData[i32StartDAnData+address++] = GetReflectionValue(i32Cy1,i32Cy2,counts, EventData);
	EventData[i32StartDAnData+address++] = GetReflectionValue(i32Cy2,i32Cy1,counts, EventData);
	if(i32HexAnode) 
	{
		EventData[i32StartDAnData+address++] = GetReflectionValue(i32Cz1,i32Cz2,counts, EventData);
		EventData[i32StartDAnData+address++] = GetReflectionValue(i32Cz2,i32Cz1,counts, EventData);
	} 
	else 
	{
		EventData[i32StartDAnData+address++] = -1.e200;
		EventData[i32StartDAnData+address++] = -1.e210;
	}

	for (__int32 ch = 0; ch<i32NumberOfChannels; ++ch)								// const 1-i32NumberOfChannels
		EventData[i32StartDAnData+address++] = double(ch+1);						// must be the last coordinates

	CCoboldParser *pParser = GetCCoboldParser();
	pParser->execute_all_commands();

	return true;
}

///////////////////////
// AnalysisFinalize
///////////////////////
// is called when analysis is stopped (not paused!)
/////////////////////////////////////////////////////////////////////////////
CDAN_API __int32 AnalysisFinalize(CDoubleArray &EventData,CDoubleArray &Parameter, CDoubleArray &WeighParameter)
{
	int iFileNum;
	CString csPathName, csBasePathName;
	int iStart, iEnd;
	bool ret = pDAnUserSP->GetMultiFileInformation(iFileNum,csPathName,csBasePathName,iStart,iEnd,bFirstFile,bLastFile);
	if(bLastFile)
		bLastFile = true;

	if(theDAnApp.SharedClassInstance) 
		theDAnApp.SharedClassInstance->bDAnIsRunning = false;

	if(racpRateAveragingInstance) 
	{
		delete racpRateAveragingInstance;
		racpRateAveragingInstance = 0;
	}

	if(pDAnUserSP)
	{
		delete pDAnUserSP;
		pDAnUserSP = nullptr;
	}
	return true;
}

//////////////////////////////////////////////////////////////////////////
// Helper functions
//////////////////////////////////////////////////////////////////////////
double GetReflectionValue(__int32 C1,__int32 C2, __int32 counts[], CDoubleArray &EventData) 
{
	double refl = -1.e100;

	if(C2 > -1 && C2 > -1) 
	{
		if(counts[C2] > 0 && counts[C1] > 1 && i32NumberOfHits > 1) 
		{
			double a = dTDCResolution * EventData[(i32StartDAqTDCData+C1*(i32NumberOfHits+1)+2)];
			double b = dTDCResolution * EventData[(i32StartDAqTDCData+C2*(i32NumberOfHits+1)+1)];
			refl = a - b;
		}
	}
	return refl;
}