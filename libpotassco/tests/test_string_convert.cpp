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
	errno = 0;
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
		REQUIRE(Potassco::string_cast<uint64_t>("umax") == static_cast<uint64_t>(-1));
	}
	SECTION("-1 is only signed value accepted as unsigned") {
		REQUIRE(Potassco::string_cast<unsigned int>("-1") == static_cast<unsigned int>(-1));
		REQUIRE_THROWS_AS(Potassco::string_cast<unsigned long long>("-2"), Potassco::bad_string_cast);
	}
	SECTION("umax does not apply to signed int") {
		REQUIRE_THROWS_AS(Potassco::string_cast<int>("umax"), Potassco::bad_string_cast);
		REQUIRE_THROWS_AS(Potassco::string_cast<long>("umax"), Potassco::bad_string_cast);
		REQUIRE_THROWS_AS(Potassco::string_cast<long long>("umax"), Potassco::bad_string_cast);
		REQUIRE_THROWS_AS(Potassco::string_cast<int64_t>("umax"), Potassco::bad_string_cast);
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
	SECTION("conversion works with long long even if errno is initially set") {
		long long mx = LLONG_MAX, y;
		unsigned long long umx = ULLONG_MAX, z;
		errno = ERANGE;
		REQUIRE((Potassco::stringTo(Potassco::toString(mx).c_str(), y) && mx == y));
		errno = ERANGE;
		StringBuilder str;
		str.appendFormat("%llu", ULLONG_MAX);
		REQUIRE((Potassco::stringTo(str.c_str(), z) && umx == z));
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
TEST_CASE("String builder", "[string]") {
	errno = 0;
	SECTION("vsprintf behaves as expected") {
		char buf[5], buf2[6];
		struct Temp {
			int operator()(char* s, std::size_t n, const char* fmt, ...) const {
				va_list args;
				va_start(args, fmt);
				int r = Potassco::vsnprintf(s, n, fmt, args);
				va_end(args);
				return r;
			}
		} t;
		REQUIRE(t(buf, sizeof(buf), "%s", "Hello") == 5);
		REQUIRE(errno == 0);
		REQUIRE(buf[4] == 0);
		REQUIRE(std::strcmp(buf, "Hell") == 0);
		REQUIRE(t(buf2, sizeof(buf2), "%s", "Hello") == 5);
		REQUIRE(errno == 0);
		REQUIRE(std::strcmp(buf2, "Hello") == 0);
	}
	SECTION("empty builder") {
		StringBuilder builder;
		REQUIRE(std::strcmp(builder.c_str(), "") == 0);
		REQUIRE(builder.size() == 0);
	}
	SECTION("append string") {
		StringBuilder builder;
		builder.append("Hello");
		REQUIRE(std::strcmp(builder.c_str(), "Hello") == 0);
		builder.append(" World");
		REQUIRE(std::strcmp(builder.c_str(), "Hello World") == 0);
		builder.append("!");
		REQUIRE(std::strcmp(builder.c_str(), "Hello World!") == 0);
	}
	SECTION("append format") {
		StringBuilder builder;
		builder.appendFormat("Hello %d", 100);
		REQUIRE(std::strcmp(builder.c_str(), "Hello 100") == 0);
		builder.appendFormat("%s - %u!!!", " World", 22u);
		REQUIRE(std::strcmp(builder.c_str(), "Hello 100 World - 22!!!") == 0);
	}
	SECTION("append format grow") {
		std::stringstream exp;
		std::srand(0);
		StringBuilder builder;
		builder.append("Start ");
		exp << builder.c_str();
		for (int i = 0; i != 100; ++i) {
			int n = std::rand();
			exp << " " << n;
			builder.appendFormat(" %d", n);
		}
		REQUIRE(std::strcmp(builder.c_str(), exp.str().c_str()) == 0);
	}
	SECTION("small buffer append") {
		StringBuilder builder;
		const char* address = builder.c_str();
		std::string str;
		do {
			builder.append("X", 1);
			str.append(1, 'X');
			REQUIRE(std::strcmp(builder.c_str(), str.c_str()) == 0);
		} while (address == builder.c_str());
		REQUIRE(builder.size() == 64);
	}
	SECTION("small buffer append format") {
		StringBuilder builder;
		const char* address = builder.c_str();
		std::string str;
		do {
			builder.appendFormat("%d", 1);
			REQUIRE(errno == 0);
			str.append(1, '1');
			REQUIRE(std::strcmp(builder.c_str(), str.c_str()) == 0);
		} while (address == builder.c_str());
		REQUIRE(builder.size() == 64);
	}
	SECTION("small buffer resize") {
		StringBuilder builder;
		builder.append(5, 'X');
		builder.resize(2);
		REQUIRE(builder.size() == 2);
		REQUIRE(std::strcmp(builder.c_str(), "XX") == 0);
		builder.resize(4, '^');
		REQUIRE(builder.size() == 4);
		REQUIRE(std::strcmp(builder.c_str(), "XX^^") == 0);
		builder[2] = 'Y';
		builder[3] = 'Z';
		REQUIRE(std::strcmp(builder.c_str(), "XXYZ") == 0);
	}
	SECTION("append to string") {
		std::string exp(1024, '?');
		std::string res;
		StringBuilder sb(res);
		for (std::size_t i = 0; i != exp.size(); ++i) {
			sb.append("?");
			REQUIRE(res == exp.substr(0, i + 1));
			REQUIRE(std::strcmp(sb.c_str(), exp.substr(0, i + 1).c_str()) == 0);
		}
		REQUIRE(res == exp);
	}
	SECTION("fixed array buffer append") {
		char buf[10];
		StringBuilder fixed(buf, sizeof(buf));
		fixed.append("123456789");
		REQUIRE(fixed.size() == 9);
		REQUIRE(fixed.c_str() == buf);
		REQUIRE(std::strcmp(fixed.c_str(), "123456789") == 0);
		fixed.append("1");
		REQUIRE(std::strcmp(fixed.c_str(), "123456789") == 0);
		REQUIRE(errno == ERANGE);
		errno = 0;
		fixed.resize(3);
		REQUIRE(std::strcmp(fixed.c_str(), "123") == 0);
		fixed.resize(7, '+');
		REQUIRE(std::strcmp(fixed.c_str(), "123++++") == 0);
	}
	SECTION("fixed array buffer append format") {
		char buf[10];
		StringBuilder fixed(buf, sizeof(buf));
		for (int i = 1; i != 10; ++i) {
			fixed.appendFormat("%d", i);
		}
		REQUIRE(fixed.size() == 9);
		REQUIRE(fixed.c_str() == buf);
		REQUIRE(std::strcmp(fixed.c_str(), "123456789") == 0);
		fixed.appendFormat("%d", 1);
		REQUIRE(std::strcmp(fixed.c_str(), "123456789") == 0);
		REQUIRE(errno == ERANGE);
		errno = 0;
	}
	SECTION("fixed array buffer append number") {
		char buf[5];
		StringBuilder fixed(buf, sizeof(buf));
		fixed.append(1234567);
		REQUIRE(errno == ERANGE);
		REQUIRE(fixed.size() == (sizeof(buf) - 1));
		REQUIRE(std::strcmp(fixed.c_str(), "1234") == 0);
		errno = 0;
	}
	SECTION("dynamic array buffer append format") {
		char buf[10];
		StringBuilder dynamic(buf, sizeof(buf), StringBuilder::Dynamic);
		dynamic.append("123456789");
		REQUIRE(dynamic.size() == 9);
		REQUIRE(dynamic.c_str() == buf);
		dynamic.appendFormat("%d", 123);
		REQUIRE(std::strcmp(dynamic.c_str(), "123456789123") == 0);
		REQUIRE(dynamic.size() == 12);
		REQUIRE(dynamic.c_str() != buf);
	}
	SECTION("test fail function") {
		try {
			fail(POTASSCO_FUNC_NAME, __LINE__, 1, "Message with %d parameters {'%s', '%s'}", 2, "Foo", "Bar");
		}
		catch (const std::logic_error& e) {
			std::string m = e.what();
			REQUIRE(m.find("Message with 2 parameters {'Foo', 'Bar'}") != std::string::npos);
		}
	}
}
}}
