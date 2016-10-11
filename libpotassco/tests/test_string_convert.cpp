//
//  Copyright (c) Benjamin Kaufmann
//
//  This is free software; you can redistribute it and/or modify
//  it under the terms of the GNU General Public License as published by
//  the Free Software Foundation; either version 2 of the License, or
//  (at your option) any later version.
//
//  This file is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU General Public License for more details.
//
//  You should have received a copy of the GNU General Public License
//  along with this program. If not, see <http://www.gnu.org/licenses/>.
#include "catch.hpp"
#include <potassco/string_convert.h>
#include <string>
#include <vector>
namespace Potassco {
namespace Test {

TEST_CASE("String conversion", "[string]") {
	SECTION("positive and negative ints convert to string") {
		REQUIRE(Potassco::string_cast(10) == "10");
		REQUIRE(Potassco::string_cast(-10) == "-10");
	}
	SECTION("unsigned -1 converts to named limit") {
		REQUIRE(Potassco::string_cast(static_cast<unsigned int>(-1)) == "umax");
		REQUIRE(Potassco::string_cast(static_cast<unsigned long>(-1)) == "umax");
		REQUIRE(Potassco::string_cast<unsigned int>("umax") == static_cast<unsigned int>(-1));
		REQUIRE(Potassco::string_cast<unsigned long>("umax") == static_cast<unsigned long>(-1));
		REQUIRE(Potassco::string_cast<unsigned long long>("umax") == static_cast<unsigned long long>(-1));
#ifdef _MSC_VER
		REQUIRE(Potassco::string_cast<unsigned __int64>("umax") == static_cast<unsigned __int64>(-1));
#endif
	}
	SECTION("-1 is only signed value accepted as unsigned") {
		REQUIRE(Potassco::string_cast<unsigned int>("-1") == static_cast<unsigned int>(-1));
		REQUIRE_THROWS_AS(Potassco::string_cast<unsigned long long>("-2"), Potassco::bad_string_cast);
	}
	SECTION("umax does not apply to signed int") {
		REQUIRE_THROWS_AS(Potassco::string_cast<int>("umax"), Potassco::bad_string_cast);
		REQUIRE_THROWS_AS(Potassco::string_cast<long>("umax"), Potassco::bad_string_cast);
		REQUIRE_THROWS_AS(Potassco::string_cast<long long>("umax"), Potassco::bad_string_cast);
#ifdef _MSC_VER
		REQUIRE_THROWS_AS(Potassco::string_cast<__int64>("umax"), Potassco::bad_string_cast);
#endif
	}
	SECTION("named limits convert to signed ints") {
		REQUIRE(Potassco::string_cast<int>("imax") == INT_MAX);
		REQUIRE(Potassco::string_cast<int>("imin") == INT_MIN);

		REQUIRE(Potassco::string_cast<long>("imax") == LONG_MAX);
		REQUIRE(Potassco::string_cast<long>("imin") == LONG_MIN);

		REQUIRE(Potassco::string_cast<long long>("imax") == LLONG_MAX);
		REQUIRE(Potassco::string_cast<long long>("imin") == LLONG_MIN);
	}

	SECTION("double converts to string") {
		REQUIRE(Potassco::string_cast(10.2) == "10.2");
	}
	SECTION("double conversion is reversible") {
		const double d = 0.00000001;
		REQUIRE(Potassco::string_cast<double>(Potassco::string_cast(d)) == d);
	}
	SECTION("Pairs can be converted") {
		const std::pair<int, bool> p(10, false);
		REQUIRE(Potassco::string_cast(p) == "10,false");
		REQUIRE((Potassco::string_cast<std::pair<int, bool> >("10,false") == p));

		typedef std::pair<int, int> IntPair;
		IntPair x;
		std::string value("(1,2)");
		bool ok = Potassco::string_cast(value, x);
		REQUIRE(ok);
		REQUIRE(x == IntPair(1, 2));
		REQUIRE(Potassco::string_cast("7", x));
		REQUIRE(x == IntPair(7, 2));

		REQUIRE(!Potassco::string_cast("9,", x));
		REQUIRE(x == IntPair(7, 2));
	}
	SECTION("Pairs can be nested") {
		typedef std::pair<int, int> IntPair;
		std::pair<IntPair, IntPair> x;
		std::string value("((1,2),(3,4))");
		REQUIRE(Potassco::string_cast(value, x));
		REQUIRE((x.first == IntPair(1, 2) && x.second == IntPair(3, 4)));
		value = "3,4,5,6";
		REQUIRE(Potassco::string_cast(value, x));
		REQUIRE((x.first == IntPair(3, 4) && x.second == IntPair(5, 6)));
		value = "99";
		REQUIRE(Potassco::string_cast(value, x));
		REQUIRE((x.first == IntPair(99, 4) && x.second == IntPair(5, 6)));
	}
	SECTION("Sequence can be converted") {
		REQUIRE(Potassco::toString(1, 2, 3) == "1,2,3");
		REQUIRE(Potassco::toString(1, "Hallo") == "1,Hallo");
	}
	SECTION("conversion works with long long") {
		long long mx = LLONG_MAX, mn = LLONG_MIN, y;
		REQUIRE((Potassco::stringTo(Potassco::toString(mx).c_str(), y) && mx == y));
		REQUIRE((Potassco::stringTo(Potassco::toString(mn).c_str(), y) && mn == y));
	}

	SECTION("double parsing is locale-independent") {
		typedef std::pair<std::string, std::string> P;
		P lcg[] = {P("de", "DE"), P("el", "GR"), P("ru", "RU"), P("es", "ES"), P("it", "IT")};
		const char* x = 0;
#if defined(_MSC_VER) && _MSC_VER <= 1600
		x = setlocale(LC_ALL, "deu_deu");
#endif
		for (const P* it = lcg, *end = it + sizeof(lcg)/sizeof(P); it != end && !x; ++it) {
			x = setlocale(LC_ALL, std::string(it->first).append(1, '_').append(it->second).c_str());
			if (x != 0) { break; }
			x = setlocale(LC_ALL, std::string(it->first).append(1, '-').append(it->second).c_str());
		}
		if (x) {
			REQUIRE(Potassco::string_cast<double>("12.32") == 12.32);
			setlocale(LC_ALL, "C");
		}
		else {
			WARN("could not set locale - test ignored");
		}
	}

	SECTION("vectors can be converted") {
		typedef std::vector<int> Vec;
		Vec x;
		std::string value("[1,2,3,4]");
		REQUIRE(Potassco::string_cast(value, x));
		REQUIRE(x.size() == 4);
		REQUIRE(x[0] == 1);
		REQUIRE(x[1] == 2);
		REQUIRE(x[2] == 3);
		REQUIRE(x[3] == 4);
		x = Potassco::string_cast<Vec>("1,2,3");
		REQUIRE(x.size() == 3);
		REQUIRE(!Potassco::string_cast("1,2,", x));
	}
	SECTION("vectors can be nested") {
		typedef std::vector<int> Vec;
		typedef std::vector<Vec> VecVec;
		VecVec x;
		std::string value("[[1,2],[3,4]]");
		REQUIRE(Potassco::string_cast(value, x));
		REQUIRE((x.size() == 2 && x[0].size() == 2 && x[1].size() == 2));
		REQUIRE(x[0][0] == 1);
		REQUIRE(x[0][1] == 2);
		REQUIRE(x[1][0] == 3);
		REQUIRE(x[1][1] == 4);
	}
}
}}
