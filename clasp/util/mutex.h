//
// Copyright (c) 2012, Benjamin Kaufmann
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

#ifndef CLASP_UTIL_MUTEX_H_INCLUDED
#define CLASP_UTIL_MUTEX_H_INCLUDED

#include <mutex>
#include <condition_variable>

namespace Clasp { namespace mt {
using std::mutex;
using std::lock_guard;
using std::unique_lock;
using std::swap;
using std::defer_lock_t;
struct condition_variable : private std::condition_variable {
	typedef std::condition_variable base_type;
	using base_type::notify_one;
	using base_type::notify_all;
	using base_type::wait;
	using base_type::native_handle;

	inline bool wait_for(unique_lock<mutex>& lock, double timeInSecs) {
		return base_type::wait_for(lock, std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::duration<double>(timeInSecs)))
			== std::cv_status::no_timeout;
	}
};
}}
#endif
