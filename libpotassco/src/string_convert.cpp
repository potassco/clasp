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
//
#include <potassco/string_convert.h>
#include <cstdlib>
#include <climits>
#include <cerrno>
#include <cstdio>
#include <algorithm>
#if defined(_MSC_VER)
#pragma warning (disable : 4996)
#define strtod_l   _strtod_l
#define freelocale _free_locale
typedef _locale_t  my_locale_t;
inline my_locale_t default_locale() { return _create_locale(LC_ALL, "C"); }
#if _MSC_VER < 1700
inline unsigned long long strtoull(const char* str, char** endptr, int base) { return  _strtoui64(str, endptr, base); }
inline long long strtoll(const char* str, char** endptr, int base) { return  _strtoi64(str, endptr, base); }
#endif
#elif defined(__CYGWIN__) || defined (__MINGW32__)
#include <locale>
typedef std::locale my_locale_t;
static double strtod_l(const char* x, char** end, const my_locale_t& loc) {
	std::size_t xLen = std::strlen(x);
	const char* err  = x;
	Potassco::detail::input_stream<char> str(x, xLen);
	str.imbue(loc);
	double out;
	if (str >> out) {
		if (str.eof()) { err += xLen; }
		else           { err += static_cast<std::size_t>(str.tellg()); }
	}
	if (end) { *end = const_cast<char*>(err); }
	return out;
}
inline void freelocale(const my_locale_t&) {}
inline my_locale_t default_locale()        { return std::locale::classic(); }
#else
#include <xlocale.h>
typedef locale_t my_locale_t;
inline my_locale_t default_locale() { return newlocale(LC_ALL_MASK, "C", 0); }
#endif
static struct LocaleHolder {
	~LocaleHolder() { freelocale(loc_);  }
	my_locale_t loc_;
} default_locale_g = { default_locale() };

using namespace std;

namespace Potassco {
#if !defined(_MSC_VER) || _MSC_VER > 1800
int vsnprintf(char* s, size_t n, const char* format, va_list arg) {
	return std::vsnprintf(s, n, format, arg);
}
#else
int vsnprintf(char* s, size_t n, const char* format, va_list arg) {
	va_list argCopy;
	va_copy(argCopy, arg);
	int res;
	if (n == 0 || (res = std::vsnprintf(s, n, format, arg)) < 0 || size_t(res) >= n) {
		errno = 0;
		if (n) { s[n-1] = 0; }
		res = _vscprintf(format, argCopy);
	}
	va_end(argCopy);
	return res;
}
#endif
static int detectBase(const char* x) {
	if (x[0] == '0') {
		if (x[1] == 'x' || x[1] == 'X') return 16;
		if (x[1] >= '0' && x[1] <= '7') return 8;
	}
	return 10;
}

static bool empty(const char* x, const char** errPos) {
	if (x && *x) return false;
	if (errPos) { *errPos = x; }
	return true;
}

static int parsed(int tok, const char* end, const char** errPos) {
	if (errPos) *errPos = end;
	return tok;
}

static bool parseSigned(const char*& x, long long& out, long long sMin, long long sMax) {
	if (!x || !*x) {
		return false;
	}
	if ((std::strncmp(x, "imax", 4) == 0 && (out = sMax) != 0) || (std::strncmp(x, "imin", 4) == 0 && (out = sMin) != 0)) {
		x += 4;
		return true;
	}
	const char* safe = x;
	char* err;
	out = strtoll(x, &err, detectBase(x));
	if (err == safe) { return false; }
	if ((out == LLONG_MAX || out == LLONG_MIN) && errno == ERANGE) {
		errno = 0;
		strtoll(x, 0, detectBase(x));
		if (errno == ERANGE) {
			x = safe;
			return false;
		}
	}
	if (out < sMin || out > sMax) { x = safe; return false; }
	x = err;
	return true;
}

static bool parseUnsigned(const char*& x, unsigned long long& out, unsigned long long uMax) {
	if (!x || !*x || (*x == '-' && x[1] != '1')) {
		return false;
	}
	std::size_t len = 4;
	if (std::strncmp(x, "imax", len) == 0 || std::strncmp(x, "umax", len) == 0 || std::strncmp(x, "-1", len=2) == 0) {
		out = *x != 'i' ? uMax : uMax >> 1;
		x  += len;
		return true;
	}
	const char* safe = x;
	char* err;
	out = strtoull(x, &err, detectBase(x));
	if (out == ULLONG_MAX && errno == ERANGE) {
		errno = 0;
		strtoull(x, 0, detectBase(x));
		if (errno == ERANGE) {
			x = safe;
			return false;
		}
	}
	if (out > uMax) { x = safe; return false; }
	x = err;
	return true;
}

int xconvert(const char* x, bool& out, const char** errPos, int) {
	if      (empty(x, errPos))           { return 0; }
	else if (*x == '1')                  { out = true;  x += 1; }
	else if (*x == '0')                  { out = false; x += 1; }
	else if (strncmp(x, "no", 2)  == 0)  { out = false; x += 2; }
	else if (strncmp(x, "on", 2)  == 0)  { out = true;  x += 2; }
	else if (strncmp(x, "yes", 3) == 0)  { out = true;  x += 3; }
	else if (strncmp(x, "off", 3) == 0)  { out = false; x += 3; }
	else if (strncmp(x, "true", 4) == 0) { out = true;  x += 4; }
	else if (strncmp(x, "false", 5) == 0){ out = false; x += 5; }
	return parsed(1, x, errPos);
}
int xconvert(const char* x, char& out, const char** errPos, int) {
	if (empty(x, errPos))     { return 0; }
	if ((out = *x++) == '\\') {
		switch(*x) {
			case 't': out = '\t'; ++x; break;
			case 'n': out = '\n'; ++x; break;
			case 'v': out = '\v'; ++x; break;
			default: break;
		}
	}
	return parsed(1, x, errPos);
}
int xconvert(const char* x, int& out, const char** errPos, int) {
	long long temp;
	if (parseSigned(x, temp, INT_MIN, INT_MAX)) {
		out = static_cast<int>(temp);
		return parsed(1, x, errPos);
	}
	return parsed(0, x, errPos);
}

int xconvert(const char* x, unsigned& out, const char** errPos, int) {
	unsigned long long temp = 0;
	if (parseUnsigned(x, temp, UINT_MAX)) {
		out = static_cast<unsigned>(temp);
		return parsed(1, x, errPos);
	}
	return parsed(0, x, errPos);
}

int xconvert(const char* x, long& out, const char** errPos, int) {
	long long temp;
	if (parseSigned(x, temp, LONG_MIN, LONG_MAX)) {
		out = static_cast<long>(temp);
		return parsed(1, x, errPos);
	}
	return parsed(0, x, errPos);
}

int xconvert(const char* x, unsigned long& out, const char** errPos, int) {
	unsigned long long temp = 0;
	if (parseUnsigned(x, temp, ULONG_MAX)) {
		out = static_cast<unsigned long>(temp);
		return parsed(1, x, errPos);
	}
	return parsed(0, x, errPos);
}

#if defined(LLONG_MAX)
int xconvert(const char* x, long long& out, const char** errPos, int) {
	int tok = parseSigned(x, out, LLONG_MIN, LLONG_MAX);
	return parsed(tok, x, errPos);
}
int xconvert(const char* x, unsigned long long& out, const char** errPos, int) {
	int tok = parseUnsigned(x, out, ULLONG_MAX);
	return parsed(tok, x, errPos);
}
#endif

int xconvert(const char* x, double& out, const char** errPos, int) {
	if (empty(x, errPos)) { return 0; }
	char* err;
	out = strtod_l(x, &err, default_locale_g.loc_);
	return parsed(err != x, err, errPos);
}

int xconvert(const char* x, const char*& out, const char** errPos, int) {
	out = x;
	if (errPos) { *errPos = x + strlen(x); }
	return 1;
}
int xconvert(const char* x, string& out, const char** errPos, int sep) {
	const char* end;
	if (sep == 0 || (end = strchr(x, char(sep))) == 0) {
		out = x;
	}
	else {
		out.assign(x, end - x);
	}
	if (errPos) { *errPos = x + out.length(); }
	return 1;
}

string& xconvert(string& out, bool b) { return out.append(b ? "true": "false"); }
string& xconvert(string& out, char c) { return out.append(1, c); }
string& xconvert(string& out, int n) { return xconvert(out, static_cast<long>(n)); }
string& xconvert(string& out, unsigned int n) { return n != static_cast<unsigned int>(-1) ? xconvert(out, static_cast<unsigned long>(n)) : out.append("umax"); }
string& xconvert(string& out, long n) {
	StringBuilder().setBuffer(out).appendFormat("%ld", n);
	return out;
}
string& xconvert(string& out, unsigned long n) {
	return n != static_cast<unsigned long>(-1) ? (StringBuilder().setBuffer(out).appendFormat("%lu", n), out) : out.append("umax");
}

#if defined(LLONG_MAX)
string& xconvert(string& out, long long n) {
	StringBuilder().setBuffer(out).appendFormat("%lld", n);
	return out;
}

string& xconvert(string& out, unsigned long long n) {
	return n != static_cast<unsigned long long>(-1)
		? (StringBuilder().setBuffer(out).appendFormat("%llu", n), out)
		: out.append("umax");
}
#endif

string& xconvert(string& out, double d) {
	StringBuilder().setBuffer(out).appendFormat("%g", d);
	return out;
}

bad_string_cast::~bad_string_cast() throw() {}
const char* bad_string_cast::what() const throw() { return "bad_string_cast"; }

StringBuilder::StringBuilder() {
	sbo_[0] = 0; setTag(sizeof(sbo_) - 1);
}
void StringBuilder::resetBuffer(uint8_t t) {
	if (tag() == (Str|Own)) {
		delete str_;
	}
	if (!t) { sbo_[0] = 0; t = sizeof(sbo_) - 1; }
	setTag(t);
}
StringBuilder::~StringBuilder() {
	resetBuffer(0);
}
void StringBuilder::clear() {
	switch (type()) {
		case Str: str_->clear(); break;
		case Buf: *(buf_.pos = buf_.beg) = 0; break;
		case Sbo: resetBuffer(0); break;
		default: assert(false);
	}
}
const char* StringBuilder::c_str() const {
	switch (type()) {
		case Str: return str_->c_str();
		case Buf: return buf_.beg;
		case Sbo: return sbo_;
		default: assert(false); return 0;
	}
}
size_t StringBuilder::size()  const {
	switch (type()) {
		case Str: return str_->size();
		case Buf: return static_cast<size_t>(buf_.pos - buf_.beg);
		case Sbo: return sizeof(sbo_) - (tag() + 1);
		default: assert(false); return 0;
	}
}
StringBuilder& StringBuilder::append(const char* str) {
	return str && *str ? append(str, std::strlen(str)) : *this;
}
StringBuilder& StringBuilder::setBuffer(std::string& s) {
	resetBuffer(Str);
	str_ = &s;
	return *this;
}
StringBuilder& StringBuilder::setBuffer(char* begin, char* end, bool allowGrow) {
	POTASSCO_ASSERT_CONTRACT(begin < end);
	resetBuffer(allowGrow ? Buf|Own : Buf);
	*(buf_.beg = buf_.pos = begin) = 0;
	*(buf_.end = end - 1) = 0;
	return *this;
}
StringBuilder::Extend StringBuilder::grow(std::size_t n) {
	Extend ret = {sbo_, n};
	Type   bft = type();
	if (bft == Sbo && tag() >= n) {
		ret.beg = sbo_ + size();
		ret.cap = tag();
		setTag(static_cast<uint8_t>(ret.cap - n));
	}
	else if (bft == Buf && (static_cast<std::size_t>(buf_.end - buf_.pos) >= n || (tag() & Own) == 0u)) {
		ret.beg = buf_.pos;
		ret.cap = static_cast<std::size_t>(buf_.end - buf_.pos);
		buf_.pos += std::min(n, ret.cap);
	}
	else if (bft == Str && n) {
		str_->append(n, '^');
		ret.beg = &(*str_)[str_->size()-n];
	}
	else if (bft == Sbo || (bft == Buf && (tag() & Own) != 0u)) {
		// alloc string
		StringBuilder temp;
		temp.resetBuffer(Str|Own);
		temp.str_ = new std::string;
		temp.str_->reserve(size() + n);
		temp.str_->append(c_str(), size());
		setTag(temp.tag());
		str_ = temp.str_;
		temp.str_ = 0;
		ret = grow(n);
	}
	return ret;
}
StringBuilder& StringBuilder::append(const char* str, std::size_t n) {
	if (type() == Str) {
		str_->append(str, n);
	}
	else {
		Extend space = grow(n);
		if (n > space.cap) {
			errno = ERANGE;
			n = space.cap;
		}
		std::memcpy(space.beg, str, n);
		space.beg[n] = 0;
	}
	return *this;
}
StringBuilder& StringBuilder::appendFormat(const char* fmt, ...) {
	const char* p = std::strchr(fmt, '%');
	std::size_t x = p ? static_cast<std::size_t>(p - fmt) : std::strlen(fmt);
	if (x) { append(fmt, x); fmt += x; }
	for (x = 0; *fmt;) {
		Extend extra = grow(x);
		if (x && !extra.cap) {
			errno = ERANGE;
			break;
		}
		va_list args;
		va_start(args, fmt);
		int n = Potassco::vsnprintf(extra.beg, extra.cap + std::size_t(x != 0), fmt, args);
		va_end(args);
		if (n < 0) { // error in conversion
			break;
		}
		else if (static_cast<std::size_t>(n) < extra.cap || x) {
			if (x == 0) { grow(static_cast<std::size_t>(n)); }
			break;
		}
		else {
			x = static_cast<std::size_t>(n);
		}
	}
	return *this;
}

void fail(const char* function, unsigned line, int type, const char* fmt, ...) {
	char buffer[1024];
	StringBuilder builder;
	builder.setBuffer(buffer, buffer + sizeof(buffer), false);
	builder.appendFormat("%s@%u: ", function, line);
	if (type == 1) {
		builder.append("contract violated: ");
	}
	if (std::strchr(fmt, '%') == 0) {
		builder.append(fmt);
	}
	else {
		std::size_t sz = builder.size();
		va_list args;
		va_start(args, fmt);
		vsnprintf(buffer + sz, sizeof(buffer)-sz, fmt, args);
		va_end(args);
	}
	throw std::logic_error(buffer);
}

} // namespace Potassco
