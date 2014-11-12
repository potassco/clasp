// 
// Copyright (c) 2006-2007, Benjamin Kaufmann
// 
// This file is part of Clasp. See http://www.cs.uni-potsdam.de/clasp/ 
// 
// Clasp is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
// 
// Clasp is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
// 
// You should have received a copy of the GNU General Public License
// along with Clasp; if not, write to the Free Software
// Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
//
#include "clasp_app.h"
/////////////////////////////////////////////////////////////////////////////////////////
// main - entry point
/////////////////////////////////////////////////////////////////////////////////////////
// #define CHECK_HEAP
#if defined (_MSC_VER) && defined(CHECK_HEAP) && _MSC_VER >= 1200
#include <crtdbg.h>
#endif
int main(int argc, char** argv) {
#if defined (_MSC_VER) && defined (CHECK_HEAP) && _MSC_VER >= 1200 
	_CrtSetDbgFlag(_CrtSetDbgFlag(_CRTDBG_REPORT_FLAG) |
					_CRTDBG_LEAK_CHECK_DF | _CRTDBG_ALLOC_MEM_DF |
	_CRTDBG_CHECK_ALWAYS_DF);

	_CrtSetReportMode( _CRT_WARN, _CRTDBG_MODE_FILE );
	_CrtSetReportFile( _CRT_WARN, _CRTDBG_FILE_STDERR );
	_CrtSetReportMode( _CRT_ERROR, _CRTDBG_MODE_FILE );
	_CrtSetReportFile( _CRT_ERROR, _CRTDBG_FILE_STDERR );
	_CrtSetReportMode( _CRT_ASSERT, _CRTDBG_MODE_FILE );
	_CrtSetReportFile( _CRT_ASSERT, _CRTDBG_FILE_STDERR );
#endif
	Clasp::Cli::ClaspApp app;
	return app.main(argc, argv);
}
