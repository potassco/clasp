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
#ifndef CLASP_HASH_H_INCLUDED
#define CLASP_HASH_H_INCLUDED
#include <potassco/platform.h>
#include <cstring>
namespace Clasp {
//! Hasher for strings.
/*!
 * \see http://research.microsoft.com/en-us/people/palarson/
 */
struct StrHash {
	std::size_t operator()(const char* str) const {
		std::size_t h = 0;
		for (const char* s = str; *s; ++s) {
			h = h * 101 + static_cast<std::size_t>(*s);
		}
		return h;
	}
};
//! Comparison function for C-strings to be used with hash map/set.
struct StrEq {
	bool operator()(const char* lhs, const char* rhs) const { return std::strcmp(lhs, rhs) == 0; }
};

}
#endif
