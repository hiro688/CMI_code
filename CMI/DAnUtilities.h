///////////////////////////////////////////////////////////////////////////
//	DAn utilities called from CoboldPC DAn
//  (c) by Klaus Ullmann-Pfleger & RoentDek Handels GmbH
//
//  V1.0 - 31.01.2002
//  V1.1 - 24.07.2008	(by A. Czasch)
///////////////////////////////////////////////////////////////////////////

// Parameter 1000 = Conversion Parameter for RAW data
#define TC_COUNTS	0	// Counts (no conversion)
#define TC_TIME		1	// Time (ns)
#define TC_POSITION	2	// Point (mm)

// Parameter 1001 = Autonoise (for floating point coordinates)
#define AN_OFF		0	// Autonoise off
#define	AN_ON		1	// Autonoise on

// Parameter 1002 = Hex-Anode calculations
#define	HA_OFF		0	// no Hex-Anode
#define	HA_ON		1	// Hex-Anode

// Parameter 1003 = PHI conversion
#define AF_RAD		0	// RAD [-pi..pi]
#define AF_RAD0		1	// RAD [0..2pi]
#define AF_DEG		2	// DEG [-180..180]
#define AF_DEG0		3	// DEG [0..360]

// Parameter 1004 = DNL correction (GP1/HM1 only)
#define	DNL_OFF		0	// no DNL correction
#define	DNL_ON		1	// Correction value (typically 0.31)

////////////////////////////////////////////////////////////
// 
// usefull constants
//

#define PI		3.1415926535897932384626433832795			// PI
#define PID2	(PI/2.)										// half PI
#define I_PI	(1/PI)										// one over PI

////////////////////////////////////////////////////////////
// 
// usefull functions
//
void RotateXY(double dX, double dY, double dAngle, __int32 iAFormat, double dCX, double dCY, double &dRX, double &dRY);
void OrthoToRPhi(double dX, double dY, __int32 iAFormat, double dCX, double dCY, double &dR, double &dPhi);
LPCTSTR DAnGetLastLMFName();
double Rnd();

/////////////////////////////////////////////////////////
class RateAveragingClass
{
public:
	volatile CWinThread *wtpRateAveragingCThread;
	volatile unsigned __int32 ui32Rate;
	volatile double dIntegrationTime; // in seconds
	volatile bool bPleaseTerminateThread;
	volatile bool bThreadIsRunning;
	volatile double dOldTimestamp;

	volatile unsigned __int32 ui32EventCounter;
public:
	// constructor
	RateAveragingClass():bPleaseTerminateThread(false),
							dIntegrationTime(1.),
							ui32EventCounter(0),
							ui32Rate(0),
							dOldTimestamp(0.),
							bThreadIsRunning(false)  
	{
	}

	// destructor
	~RateAveragingClass() 
	{
		if(this->bThreadIsRunning) 
			TerminateThread();
	}

	void StartThread() 
	{
		this->wtpRateAveragingCThread = AfxBeginThread(&RateAveragingThread ,(LPVOID)this,THREAD_PRIORITY_NORMAL,0,0,nullptr);
	}

	void TerminateThread() 
	{
		while (this->bThreadIsRunning) 
		{
			this->bPleaseTerminateThread = true; 
			Sleep(30);
		}
	}

	void CheckTimestamp(double dNewTimestamp) 
	{
		if(dNewTimestamp != 0.) 
		{
			if(dNewTimestamp - dOldTimestamp > dIntegrationTime) 
			{
				ui32Rate = (unsigned __int32)(double(ui32EventCounter) / dIntegrationTime);
				ui32EventCounter = 0;
				dOldTimestamp = dNewTimestamp;
			}
		}
	}

	static UINT RateAveragingThread(LPVOID vpClassPointer)
	{
		RateAveragingClass *racMyEvent = (RateAveragingClass*)vpClassPointer;
		racMyEvent->bThreadIsRunning = true;

		while (!racMyEvent->bPleaseTerminateThread) 
		{
			if(racMyEvent->dIntegrationTime < 0.1) 
				racMyEvent->dIntegrationTime = 0.1;
			unsigned __int32 ui32Loops = (unsigned __int32)(racMyEvent->dIntegrationTime*5.0);
			for (unsigned __int32 i=0;i < ui32Loops;++i) 
			{
				Sleep(200);
				if(racMyEvent->bPleaseTerminateThread) 
					break;
			}
			if(racMyEvent->bPleaseTerminateThread) 
				break;
			Sleep((unsigned __int32)(racMyEvent->dIntegrationTime*1000.)-ui32Loops*200);
			racMyEvent->ui32Rate = (unsigned __int32)(racMyEvent->ui32EventCounter / racMyEvent->dIntegrationTime);
			racMyEvent->ui32EventCounter = 0;
		}

		racMyEvent->ui32Rate = 0;
		racMyEvent->ui32EventCounter = 0;
		racMyEvent->bThreadIsRunning = false;

		AfxEndThread(1,TRUE);
		return TRUE;
	}
};