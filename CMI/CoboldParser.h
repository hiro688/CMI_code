// CoboldParser.h : main header file for the CoboldParser DLL
//

#pragma once

#ifndef __AFXWIN_H__
	#error "include 'stdafx.h' before including this file for PCH"
#endif

// CCoboldParserApp
// See CoboldParser.cpp for the implementation of this class
//

class CCoboldParserApp : public CWinApp
{
public:
	CCoboldParserApp();

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

#ifdef COBOLDPARSER_EXPORTS
#define CPARSER_API __declspec(dllexport)
#else
#define CPARSER_API __declspec(dllimport)
#endif

	//////////////////////////////////////////////////////////////////////////
	// Forward declarations
	//////////////////////////////////////////////////////////////////////////

	class CCoboldDoc;
	class CDoubleArray;
	class CUserSpectrum;
	class CCoboldParser;
	class CCoordinatesMathCommand;
	//class SharedClass;

	
//#ifdef COBOLDPARSER_EXPORTS
	CPARSER_API bool DoMathFunction(CString csInput[],unsigned __int32 ui32InputMaximumIndex, unsigned __int32 ui32WordCount);
	CPARSER_API CCoboldParser *GetCCoboldParser();
//#endif

	class CPARSER_API CCoboldParser
	{
	public:
		CCoboldParser();
		virtual ~CCoboldParser();

		__int32 find_matching_closing_bracket(CString command, __int32 index_of_left_bracket);
		void add_command_as_string(CString command);
		void add_command_as_string_helper(CString command, CString mother_command);
		double execute_single_command(__int32 index);
		void execute_all_commands();
		bool RemoveUnneededBrackets(CString &command);
		void simplify_the_command_stack();

		__int32 find_marker_index(CString marker);
		bool parse_single_command(__int32 index);
		void parse_all_commands();
		void reset();

		void insert_command_as_string(CString command, __int32 index);
		void strip_white_spaces(CString &command);
		void dissect_all_commands();
		void set_helping_brackets_in_command(CString &command);
		__int32 get_length_of_following_operand(CString command, __int32 start_index);
		__int32 get_length_of_preceding_operand(CString command, __int32 start_index);
		__int32 find_char_after_index(CString command, __int32 index, CString target_chars);
		void insert_brackets_around_all_occurences_of_char(CString &command, CString target_chars);
		void insert_brackets_around_all_occurences_of_numbers(CString &command);
		__int32 find_next_bool_operator(CString command, __int32 index, __int32 &length);
		__int32 find_next_bool_log_operator(CString command, __int32 index, __int32 &length);
		void insert_brackets_around_all_occurences_of_bool_operators(CString &command, __int32 type);
		bool isNumeric(const char* pszInput, __int32 nNumberBase);
		bool isNumeric(CString csInput, __int32 nNumberBase);
		void strip_brackets(CString &input);
		void extract_operands(CString input, CString &op_a, CString &csOperator, CString &op_b);
		void extract_3operands(CString input, CString &op_a, CString &csOperator, CString &op_b, CString &op_c);
		void remove_command_from_commandstack(__int32 index);
		void add_error_message(char* message);
		void add_error_message(__int32 ivalue);
		void add_error_message(double dvalue);
		char* get_error_message();

	protected:
		CCoboldDoc *m_pDoc;
		CDoubleArray &Parameter;
		CDoubleArray &EventData;

		CCoordinatesMathCommand **command_stack;
		CDoubleArray *pInternalStack;

		__int32 iCommentLevel;
		__int32 iHighestCoordinatesIndex;
		__int32 iHighestInternalStackIndex;
		__int32 iScopeLevel;
		bool	all_commands_parsed;
		__int32	last_error;
		char error_messages[1000];
		__int32 iNumberofCommands;
		__int32 size_of_command_stack;
		CUserSpectrum *pCPUserSP;
	};


#ifdef __cplusplus
}
#endif
