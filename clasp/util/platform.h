//
// Copyright (c) 2006-2016, Benjamin Kaufmann
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
//! \file
//! \brief Global and platform-dependent stuff.
#ifndef CLASP_PLATFORM_H_INCLUDED
#define CLASP_PLATFORM_H_INCLUDED
#ifdef _MSC_VER
#pragma once
#endif
#if !defined(CLASP_HAS_THREADS)
#error Invalid include context - shall be included by config.h
#endif
#include <potassco/platform.h>
#if CLASP_HAS_THREADS
#include <atomic>
namespace Clasp { namespace mt {
//! Thin wrapper around std::atomic with sequentially consistent loads and stores.
template <class T>
class atomic : private std::atomic<T> {
public:
	typedef std::atomic<T> native_type;
	native_type& native() { return *this; }

	T operator=(T value) { return native_type::operator=(value); }
	operator T() const { return native_type::operator T(); }

	using native_type::operator+=;
	using native_type::operator-=;
	using native_type::operator++;
	using native_type::operator--;
	T compare_and_swap(T new_value, T comparand) {
		native_type::compare_exchange_strong(comparand, new_value);
		return comparand;
	}
	T fetch_and_store(T value) { return native_type::exchange(value); }
	T fetch_and_or(T value)    { return native_type::fetch_or(value); }
	T fetch_and_and(T value)   { return native_type::fetch_and(value); }
};
}
template <class T>
struct Atomic_t { typedef Clasp::mt::atomic<T> type; };
}
#else
namespace Clasp {
//! Forwards to plain T, which is not necessarily atomic and therefore not thread-safe.
template <class T>
struct Atomic_t {
	typedef struct Plain {
		T operator=(T nv) { return (val = nv); }
		operator T () const { return val; }
		operator T&() { return val; }
		T compare_and_swap(T nVal, T eVal) {
			if (val == eVal) { val = nVal; }
			else { eVal = val; }
			return eVal;
		}
		T fetch_and_store(T nVal) {
			T p = val;
			val = nVal;
			return p;
		}
		T fetch_and_or(T value) { return fetch_and_store(val | value); }
		T fetch_and_and(T value) { return fetch_and_store(val & value); }
		T val;
	} type;
};
}
#endif

typedef uint64_t  uint64;
typedef uint32_t  uint32;
typedef uint16_t  uint16;
typedef uint8_t   uint8;
typedef uintptr_t uintp;
typedef int64_t   int64;
typedef int32_t   int32;
typedef int16_t   int16;
typedef int8_t    int8;

#if _WIN32||_WIN64
inline void* alignedAlloc(size_t size, size_t align) { return _aligned_malloc(size, align); }
inline void  alignedFree(void* p)                    { _aligned_free(p); }
#else
inline void* alignedAlloc(size_t size, size_t align) {
#	if !defined(__CYGWIN__)
	void* result = 0;
	return posix_memalign(&result, align, size) == 0 ? result : static_cast<void*>(0);
#	else
	return memalign(align, size);
#	endif
}
inline void alignedFree(void* p) { free(p); }
#endif


#if !defined(CLASP_HAS_STATIC_ASSERT) || CLASP_HAS_STATIC_ASSERT == 0
template <bool> struct static_assertion;
template <>     struct static_assertion<true> {};
#ifndef __GNUC__
#define static_assert(x, message) typedef bool clasp_static_assertion[sizeof(static_assertion< (x) >)]
#else
#define static_assert(x, message) typedef bool clasp_static_assertion[sizeof(static_assertion< (x) >)]  __attribute__((__unused__))
#endif
#endif

#define CLASP_FAIL_IF(exp, ...) POTASSCO_FAIL_IF(exp, __VA_ARGS__)

#if defined(CLASP_NO_ASSERT_CONTRACT) && CLASP_NO_ASSERT_CONTRACT
#define CLASP_ASSERT_CONTRACT_MSG(exp, msg)
#else
#define CLASP_ASSERT_CONTRACT_MSG(exp, msg) POTASSCO_ASSERT_CONTRACT_MSG(exp, msg)
#endif

#define CLASP_ASSERT_CONTRACT(exp) CLASP_ASSERT_CONTRACT_MSG(exp, #exp)

#endif

