//
// Copyright (c) 2016, Benjamin Kaufmann
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
#ifndef POTASSCO_PLATFORM_H_INCLUDED
#define POTASSCO_PLATFORM_H_INCLUDED
#include <cstddef>
#include <cassert>
#include <string>
#if defined(_MSC_VER)
#define POTASSCO_STRING2(x) #x
#define POTASSCO_STRING(x) POTASSCO_STRING2(x)
#define POTASSCO_PRAGMA_TODO(X) __pragma(message(__FILE__ "(" POTASSCO_STRING(__LINE__) ") : TODO: " X))
#define POTASSCO_FUNC_NAME __FUNCTION__
#define POTASSCO_WARNING_BEGIN_RELAXED \
	__pragma(warning(push))\
	__pragma(warning (disable : 4200))

#define POTASSCO_WARNING_END_RELAXED \
	__pragma(warning(pop))

#elif defined(__GNUC__) || defined(__clang__)
#if !defined(__STDC_FORMAT_MACROS)
#define __STDC_FORMAT_MACROS
#endif
#if !defined(__STDC_LIMIT_MACROS)
#define __STDC_LIMIT_MACROS
#endif
#define POTASSCO_FUNC_NAME __PRETTY_FUNCTION__
#define POTASSCO_APPLY_PRAGMA(x) _Pragma (#x)
#define POTASSCO_PRAGMA_TODO(x) POTASSCO_APPLY_PRAGMA(message ("TODO: " #x))
#	if defined(__clang__)
#		define POTASSCO_WARNING_BEGIN_RELAXED \
		_Pragma("clang diagnostic push") \
		_Pragma("clang diagnostic ignored \"-Wzero-length-array\"")
#		define POTASSCO_WARNING_END_RELAXED _Pragma("clang diagnostic pop")
#	else
#		define POTASSCO_WARNING_BEGIN_RELAXED \
		_Pragma("GCC diagnostic push")\
		_Pragma("GCC diagnostic ignored \"-Wpragmas\"")\
		_Pragma("GCC diagnostic ignored \"-Wpedantic\"")\
		_Pragma("GCC diagnostic ignored \"-pedantic\"")
#		define POTASSCO_WARNING_END_RELAXED _Pragma("GCC diagnostic pop")
#endif
#else
#define POTASSCO_FUNC_NAME __FILE__
#define POTASSCO_WARNING_BEGIN_RELAXED
#define POTASSCO_WARNING_END_RELAXED
#endif
#include <inttypes.h>

#if !defined(POTASSCO_ENABLE_PRAGMA_TODO) || POTASSCO_ENABLE_PRAGMA_TODO==0
#undef POTASSCO_PRAGMA_TODO
#define POTASSCO_PRAGMA_TODO(X)
#endif

#if UINTPTR_MAX > UINT64_MAX
#error Unsupported platform!
#endif

namespace Potassco {

class StringBuilder {
public:
	StringBuilder();
	~StringBuilder();
	void clear();
	const char* c_str() const;
	size_t      size()  const;
	StringBuilder& setBuffer(std::string& s);
	StringBuilder& setBuffer(char* begin, char* end, bool allowGrow);
	StringBuilder& appendFormat(const char* fmt, ...);
	StringBuilder& append(const char* str);
	StringBuilder& append(const char* str, std::size_t len);
private:
	StringBuilder(const StringBuilder&);
	StringBuilder& operator=(const StringBuilder&);
	enum Type { Sbo = 0u, Str = 64u, Buf = 128u };
	enum Flag { Own = 1u };
	void resetBuffer(uint8_t type);
	void setTag(uint8_t t) { reinterpret_cast<uint8_t&>(sbo_[63]) = t; }
	typedef std::string* String;
	struct Buffer { char* beg, *pos, *end; };
	struct Extend { char* beg; std::size_t cap; };
	uint8_t  tag()  const { return static_cast<uint8_t>(sbo_[63]); }
	Type     type() const { return static_cast<Type>(tag() & uint8_t(Str|Buf)); }
	Extend   grow(std::size_t n);
	union {
		String str_;
		Buffer buf_;
		char   sbo_[64];
	};
};

} // namespace Potassco


#define POTASSCO_FAIL_IF(exp, ...) \
	(void)( (!(exp)) || (throw std::logic_error(Potassco::StringBuilder().appendFormat(__VA_ARGS__).c_str()), 0))

#define POTASSCO_ASSERT_CONTRACT_MSG(exp, msg) \
	(void)( (!!(exp)) || (throw std::logic_error(Potassco::StringBuilder().appendFormat("%s@%d: contract violated: %s", POTASSCO_FUNC_NAME, __LINE__, (msg)).c_str()), 0))

#define POTASSCO_ASSERT_CONTRACT(exp) POTASSCO_ASSERT_CONTRACT_MSG(exp, #exp)

#endif
