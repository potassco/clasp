// 
// Copyright (c) 2006, Benjamin Kaufmann
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

#include <cppunit/CompilerOutputter.h>
#include <cppunit/extensions/TestFactoryRegistry.h>
#include <cppunit/TextTestProgressListener.h>
#include <cppunit/Exception.h>
#include <cppunit/ui/text/TestRunner.h>
#include <cppunit/TextTestResult.h>
#include <string.h>
#include <stdexcept>
#if defined (_MSC_VER) && _MSC_VER >= 1200
#include <crtdbg.h>
#endif
// #define CHECK_HEAP 1;

class CmdLineRunner : public CPPUNIT_NS::TextUi::TestRunner {
public:
	using CPPUNIT_NS::TextUi::TestRunner::run;
	bool run(const std::string& prefix, char** argv, int num) {
		using namespace CPPUNIT_NS;
		if (num == 0) { // run all tests
			return TextUi::TestRunner::run();
		}
		TextTestProgressListener progress;
		m_eventManager->addListener( &progress );
		for (int i = 0; i != num; ++i) {
			std::string path = strncmp(argv[i], prefix.c_str(), prefix.length()) != 0 ? prefix + argv[i] : argv[i];
			try { TestRunner::run(*m_eventManager, path); }
			catch (const std::invalid_argument& e) {
				m_eventManager->addError(m_suite, new Exception(Message(e.what()), CPPUNIT_SOURCELINE()));
			}
		}
		m_eventManager->removeListener( &progress );
		printResult( true );
		return m_result->wasSuccessful();
	}
};

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
	CmdLineRunner runner;
	// Change the default outputter to a compiler error format outputter.
#if defined (_MSC_VER)
	runner.setOutputter( new CPPUNIT_NS::CompilerOutputter( &runner.result(), std::cout ) );
#else
	runner.setOutputter( new CPPUNIT_NS::CompilerOutputter( &runner.result(), std::cout, "%p:%l:" ) );
#endif
	// Add all registered tests.
	runner.addTest( CPPUNIT_NS::TestFactoryRegistry::getRegistry().makeTest() );
	// Run selected tests.
	return 1 - int(runner.run("Clasp::Test::", argv + 1, argc - 1));
}
