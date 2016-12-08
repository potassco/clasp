//
// Copyright (c) 2015, Benjamin Kaufmann
//
// This file is part of Potassco.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//

#include <potassco/aspif.h>
#include <potassco/aspif_text.h>
#include <potassco/convert.h>
#include <potassco/application.h>
#include <potassco/program_opts/typed_value.h>
#include <fstream>
#include <iostream>
#include <cctype>
#include <cstdlib>

using namespace Potassco::ProgramOptions;

class LpConvert : public Potassco::Application {
public:
	virtual const char* getName()       const { return "lpconvert"; }
	virtual const char* getVersion()    const { return "1.0.0"; }
	virtual PosOption   getPositional() const { return &positional; }
	virtual const char* getUsage()      const {
		return
			"[options] [<file>]\n"
			"Convert program in <file> or standard input";
	}
	virtual void initOptions(OptionContext& root);
	virtual void validateOptions(const OptionContext&, const ParsedOptions&, const ParsedValues&) {}
	virtual void setup() {}
	virtual void run();
private:
	static bool positional(const std::string&, std::string& optOut) {
		optOut = "input";
		return true;
	}
	static int error(int line, const char* what) {
		fprintf(stderr, "*** ERROR: In line %d: %s\n", line, what);
		static_cast<LpConvert*>(Application::getInstance())->exit(EXIT_FAILURE);
		return EXIT_FAILURE;
	}
	std::string input_;
	std::string output_;
	bool potassco_;
	bool filter_;
	bool text_;
};

void LpConvert::initOptions(OptionContext& root) {
	OptionGroup convert("Conversion Options");
	convert.addOptions()
		("input,i,@2", storeTo(input_),  "Input file")
		("potassco,p", flag(potassco_ = false), "Enable potassco extensions")
		("filter,f"  , flag(filter_ = false), "Hide converted potassco predicates")
		("output,o"  , storeTo(output_)->arg("<file>"), "Write output to <file> (default: stdout)")
		("text,t"    , flag(text_ = false), "Convert to ground text format")
	;
	root.add(convert);
}
void LpConvert::run() {
	std::ifstream iFile;
	std::ofstream oFile;
	if (!input_.empty() && input_ != "-") {
		iFile.open(input_.c_str());
		POTASSCO_REQUIRE(iFile.is_open(), std::runtime_error, "Could not open input file!");
	}
	if (!output_.empty() && output_ != "-") {
		POTASSCO_REQUIRE(input_ != output_, std::runtime_error, "Input and output must be different!");
		oFile.open(output_.c_str());
		POTASSCO_REQUIRE(oFile.is_open(), std::runtime_error, "Could not open output file!");
	}
	std::istream& in = iFile.is_open() ? iFile : std::cin;
	std::ostream& os = oFile.is_open() ? oFile : std::cout;
	Potassco::AspifTextOutput text(os);
	POTASSCO_REQUIRE(in.peek() == 'a' || std::isdigit(in.peek()), std::runtime_error, "Unrecognized input format!");
	if (in.peek() == 'a') {
		Potassco::SmodelsOutput  writer(os, potassco_, 0);
		Potassco::SmodelsConvert smodels(writer, potassco_);
		Potassco::readAspif(in, !text_ ? static_cast<Potassco::AbstractProgram&>(smodels) : text, &error);
	}
	else {
		Potassco::AspifOutput aspif(os);
		Potassco::SmodelsInput::Options opts;
		if (potassco_) {
			opts.enableClaspExt().convertEdges().convertHeuristic();
			if (filter_) { opts.dropConverted(); }
		}
		Potassco::readSmodels(in, !text_? static_cast<Potassco::AbstractProgram&>(aspif) : text, &error, opts);
	}
	iFile.close();
	oFile.close();
}

int main(int argc, char** argv) {
	LpConvert app;
	return app.main(argc, argv);
}
