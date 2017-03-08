//
// Copyright (c) 2006-2017 Benjamin Kaufmann
//
// This file is part of Clasp. See http://www.cs.uni-potsdam.de/clasp/
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// IN THE SOFTWARE.
//

#include <cppunit/CompilerOutputter.h>
#include <cppunit/extensions/TestFactoryRegistry.h>
#include <cppunit/TextTestProgressListener.h>
#include <cppunit/Exception.h>
#include <cppunit/ui/text/TestRunner.h>
#include <cppunit/TextTestResult.h>
#include <string.h>
#include <stdexcept>
#include <stdio.h>
#include <limits.h>
#if defined (_MSC_VER) && _MSC_VER >= 1200
#include <crtdbg.h>
#endif
//#define CHECK_HEAP 1

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

void dump(CPPUNIT_NS::Test* root, int level, int maxLevel) {
	if (root && level != maxLevel) {
		printf("%s\n", root->getName().c_str());
		for (int i = 0; i < root->getChildTestCount(); i++) {
			CPPUNIT_NS::Test* c = root->getChildTestAt(i);
			if (level + 1 < maxLevel) { dump(c, level + 1, maxLevel); }
			else {
				printf("%s\n", c->getName().c_str());
			}
		}
	}
}
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
	if (argc == 2) {
		if (strcmp(argv[1], "--list") == 0) {
			dump(CPPUNIT_NS::TestFactoryRegistry::getRegistry().makeTest(), 0, 1);
			return 0;
		}
		else if (strcmp(argv[1], "--list-all") == 0) {
			dump(CPPUNIT_NS::TestFactoryRegistry::getRegistry().makeTest(), 0, INT_MAX);
			return 0;
		}
	}
	// Add all registered tests.
	runner.addTest( CPPUNIT_NS::TestFactoryRegistry::getRegistry().makeTest() );
	// Run selected tests.
	return 1 - int(runner.run("Clasp::Test::", argv + 1, argc - 1));
}
