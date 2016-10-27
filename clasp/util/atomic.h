//
// Copyright (c) 2010-2016, Benjamin Kaufmann
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

#ifndef CLASP_UTIL_ATOMIC_H_INCLUDED
#define CLASP_UTIL_ATOMIC_H_INCLUDED
#ifdef _MSC_VER
#pragma once
#endif
/*!
 * \file
 * \brief Atomic types suitable for the active thread configuration.
 *
 * \note If libclasp is not configured with thread support,
 * types from this file are not necessarily atomic and must not be accessed
 * from multiple threads.
 */

namespace Clasp {
	//! Possible libclasp thread configurations.
	enum ThreadConfig {
		clasp_single_threaded = 0,
		clasp_multi_threaded  = 1
	};
	//! Type selector for selecting atomic type based on active thread configuration.
	template <class T, ThreadConfig tc = static_cast<ThreadConfig>(CLASP_HAS_THREADS)>
	struct Atomic_t;

	//! Selects a type that is not necessarily atomic and therefore not thread-safe.
	template <class T>
	struct Atomic_t<T, clasp_single_threaded> {
		typedef struct Plain {
			T operator=(T nv)   { return (val = nv); }
			operator T () const { return val; }
			operator T&()       { return val; }
			T compare_and_swap(T nVal, T eVal) {
				if (val == eVal) { val = nVal; } else { eVal = val; }
				return eVal;
			}
			T fetch_and_store(T nVal) {
				T p = val;
				val = nVal;
				return p;
			}
			T val;
		} type;
	};
}

#if defined(CLASP_HAS_THREADS) && CLASP_HAS_THREADS == 1
#include <atomic>
namespace Clasp { namespace mt {
	//! Atomic type with sequentially consistent loads and stores.
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
}}
namespace Clasp {
	//! Selects an atomic ype suitable for multi-threading.
	template <class T>
	struct Atomic_t<T, clasp_multi_threaded> {
		typedef Clasp::mt::atomic<T> type;
	};
}
#endif
#endif
