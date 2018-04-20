//
// Copyright (c) 2016-2018 Benjamin Kaufmann
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
#include <clasp/statistics.h>
#include <clasp/util/misc_types.h>
#include <clasp/util/hash.h>
#include <potassco/match_basic_types.h>
#include <potassco/string_convert.h>
#include POTASSCO_EXT_INCLUDE(unordered_map)
#include POTASSCO_EXT_INCLUDE(unordered_set)
#include <stdexcept>
#include <cstring>
#ifdef _MSC_VER
#pragma warning (disable : 4996)
#endif
namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// StatisticObject
/////////////////////////////////////////////////////////////////////////////////////////
StatisticObject::RegVec StatisticObject::types_;
StatisticObject::StatisticObject() : handle_(0) {}
StatisticObject::StatisticObject(const void* obj, uint32 type) {
	handle_  = static_cast<uint64>(type) << 48;
	handle_ |= static_cast<uint64>(reinterpret_cast<uintp>(obj));
}
const void* StatisticObject::self() const {
	static const uint64 ptrMask = bit_mask<uint64>(48) - 1;
	return reinterpret_cast<const void*>(static_cast<uintp>(handle_ & ptrMask));
}
const StatisticObject::I* StatisticObject::tid() const {
	return types_.at(static_cast<uint32>(handle_ >> 48));
}
StatisticObject::Type StatisticObject::type() const {
	return !empty() ? tid()->type : Potassco::Statistics_t::Empty;
}
bool StatisticObject::empty() const {
	return handle_ == 0;
}
uint32 StatisticObject::size() const {
	switch (type()) {
		default: throw std::logic_error("invalid object");
		case Potassco::Statistics_t::Value: return 0;
		case Potassco::Statistics_t::Map:   return static_cast<const M*>(tid())->size(self());
		case Potassco::Statistics_t::Array: return static_cast<const A*>(tid())->size(self());
	}
}
const char* StatisticObject::key(uint32 i) const {
	POTASSCO_REQUIRE(type() == Potassco::Statistics_t::Map, "type error");
	return static_cast<const M*>(tid())->key(self(), i);
}
static inline StatisticObject check(StatisticObject o) {
	if (!o.empty()) { return o; }
	throw std::out_of_range("StatisticObject");
}
StatisticObject StatisticObject::at(const char* k) const {
	POTASSCO_REQUIRE(type() == Potassco::Statistics_t::Map, "type error");
	return check(static_cast<const M*>(tid())->at(self(), k));
}
StatisticObject StatisticObject::operator[](uint32 i) const {
	POTASSCO_REQUIRE(type() == Potassco::Statistics_t::Array, "type error");
	return check(static_cast<const A*>(tid())->at(self(), i));
}
double StatisticObject::value() const {
	POTASSCO_REQUIRE(type() == Potassco::Statistics_t::Value, "type error");
	return static_cast<const V*>(tid())->value(self());
}
std::size_t StatisticObject::hash() const {
	return POTASSCO_EXT_NS::hash<uint64>()(toRep());
}
uint64 StatisticObject::toRep() const {
	return handle_;
}
StatisticObject StatisticObject::fromRep(uint64 x) {
	if (!x) { return StatisticObject(0, 0); }
	StatisticObject r;
	r.handle_ = x;
	POTASSCO_REQUIRE(r.tid() != 0 && (reinterpret_cast<uintp>(r.self()) & 3u) == 0, "invalid key");
	return r;
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspStatistics
/////////////////////////////////////////////////////////////////////////////////////////
struct ClaspStatistics::Impl {
	typedef POTASSCO_EXT_NS::unordered_map<uint64, uint32> RegMap;
	struct StatsArr : PodVector<StatisticObject>::type {
		StatisticObject toStats() const { return StatisticObject::array(this); }
	};
	typedef double StatsVal;
	typedef POTASSCO_EXT_NS::unordered_set<const char*, StrHash, StrEq> StringSet;

	Impl() : gc_(0), rem_(0) {}
	~Impl() {
		while (!objects.empty()) {
			StatisticObject obj = objects.back();
			destroy(obj.type(), const_cast<void*>(obj.self()));
			objects.pop_back();
		}
		for (StringSet::iterator it = strings.begin(), end = strings.end(); it != end; ++it) {
			delete[] *it;
		}
	}

	void destroy(Type t, void* ptr) {
		switch (t) {
			case Potassco::Statistics_t::Value:
				delete static_cast<StatsVal*>(ptr);
				break;
			case Potassco::Statistics_t::Map:
				delete static_cast<StatsMap*>(ptr);
				break;
			case Potassco::Statistics_t::Array:
				delete static_cast<StatsArr*>(ptr);
				break;
			default: break;
		}
	}
	Key_t add(Type t) {
		StatisticObject obj;
		switch (t) {
			case Potassco::Statistics_t::Value:
				obj = StatisticObject::value(new StatsVal(0.0));
				break;
			case Potassco::Statistics_t::Map:
				obj = StatisticObject::map(new StatsMap());
				break;
			case Potassco::Statistics_t::Array:
				obj = StatisticObject::array(new StatsArr());
				break;
			default:
				POTASSCO_REQUIRE(false, "unsupported statistic object type");
				break;
		}
		objects.push_back(obj);
		return add(obj);
	}
	template <class T>
	static T*        pointer(Key_t k) { return static_cast<T*>(const_cast<void*>(StatisticObject::fromRep(k).self())); }
	static Type type(Key_t key)       { return StatisticObject::fromRep(key).type(); }
	static StatsMap* map(Key_t k)     { requireType(k, Potassco::Statistics_t::Map); return pointer<StatsMap>(k); }
	static StatsArr* array(Key_t k)   { requireType(k, Potassco::Statistics_t::Array); return  pointer<StatsArr>(k); }
	static StatsVal* value(Key_t k)   { requireType(k, Potassco::Statistics_t::Value); return  pointer<StatsVal>(k); }
	static Key_t     key(const StatisticObject& obj) { return static_cast<Key_t>(obj.toRep()); }
	static void      requireType(Key_t k, Type t)    { POTASSCO_REQUIRE(type(k) == t, "type error"); }
	Key_t            userroot() const                { return key(objects[0]); }
	const char*      string(const char* s) {
		StringSet::iterator it = strings.find(s);
		if (it != strings.end())
			return *it;
		return *strings.insert(it, std::strcpy(new char[std::strlen(s) + 1], s));
	}


	Key_t add(const StatisticObject& o) {
		uint64 k = o.toRep();
		map_[k] = gc_;
		return k;
	}
	bool remove(const StatisticObject& o) {
		std::size_t rem = map_.erase(o.toRep());
		StatsArr::iterator i = std::find(objects.begin(), objects.end(), o);
		if ( i != objects.end()) {
			destroy(i->type(), const_cast<void*>(i->self()));
			objects.erase(i);
		}
		return rem != 0;
	}
	StatisticObject get(Key_t k) const {
		RegMap::const_iterator it = map_.find(k);
		POTASSCO_REQUIRE(it != map_.end() && it->second == gc_, "invalid key");
		return StatisticObject::fromRep(k);
	}
	void update(const StatisticObject& root) {
		++gc_;
		rem_ += (sizeVec(map_) - visit(root));
		if (rem_ > (map_.size() >> 1)) {
			for (RegMap::iterator it = map_.begin(), end = map_.end(); it != end;) {
				if (it->second == gc_) { ++it; }
				else { it = map_.erase(it); }
			}
			rem_ = 0;
		}
	}
	uint32 visit(const StatisticObject& obj) {
		uint32 count = 0;
		RegMap::iterator it = map_.find(obj.toRep());
		if (obj.empty() || it == map_.end()) { return count; }
		it->second = gc_;
		++count;
		switch (obj.type()) {
			case Potassco::Statistics_t::Map:
				for (uint32 i = 0, end = obj.size(); i != end; ++i) { count += visit(obj.at(obj.key(i))); }
				break;
			case Potassco::Statistics_t::Array:
				for (uint32 i = 0, end = obj.size(); i != end; ++i) { count += visit(obj[i]); }
				break;
			default: break;
		}
		return count;
	}
	RegMap map_;
	uint32 gc_;
	uint32 rem_;
	PodVector<StatisticObject>::type objects;
	StringSet strings;
};

ClaspStatistics::ClaspStatistics() : root_(0), impl_(new Impl()), userroot_(impl_->add(Potassco::Statistics_t::Map)) {}
ClaspStatistics::~ClaspStatistics() {
	delete impl_;
}
StatisticObject ClaspStatistics::getObject(Key_t k) const {
	return impl_->get(k);
}
ClaspStatistics::Key_t ClaspStatistics::root() const {
	return root_;
}
ClaspStatistics::Key_t ClaspStatistics::userRoot() const {
	return userroot_;
}
Potassco::Statistics_t ClaspStatistics::type(Key_t key) const {
	return getObject(key).type();
}
size_t ClaspStatistics::size(Key_t key) const {
	return getObject(key).size();
}
ClaspStatistics::Key_t ClaspStatistics::at(Key_t arrK, size_t index) const {
	return impl_->add(getObject(arrK)[toU32(index)]);
}
ClaspStatistics::Key_t ClaspStatistics::add(Key_t object, std::size_t i, Type t) {
	Impl::StatsArr* arr = impl_->array(object);
	POTASSCO_REQUIRE(arr->size() <= i || (*arr)[i].type() == t, "redefinition error");
	while (arr->size() <= i) {
		arr->push_back(getObject(impl_->add(t)));
	}
	return impl_->key((*arr)[i]);
}
const char* ClaspStatistics::key(Key_t mapK, size_t i) const {
	return getObject(mapK).key(toU32(i));
}
ClaspStatistics::Key_t ClaspStatistics::get(Key_t key, const char* path) const {
	return impl_->add(!std::strchr(path, '.')
		? getObject(key).at(path)
		: findObject(key, path));
}
ClaspStatistics::Key_t ClaspStatistics::add(Key_t object, const char* name, Type t) {
	StatsMap* map = impl_->map(object);
	if (const StatisticObject* stat = map->find(name)) {
		POTASSCO_REQUIRE(stat->type() == t, "redefinition error");
		return impl_->key(*stat);
	}
	Key_t stat = impl_->add(t);
	map->push(impl_->string(name), getObject(stat));
	return stat;
}
double ClaspStatistics::value(Key_t key) const {
	return getObject(key).value();
}
void ClaspStatistics::set(Key_t key, double v) {
	*(impl_->value(key)) = v;
}
ClaspStatistics::Key_t ClaspStatistics::setRoot(const StatisticObject& obj) {
	return root_ = impl_->add(obj);
}
ClaspStatistics::Key_t ClaspStatistics::addUserRoot() {
	impl_->map(root_)->push(impl_->string("user_defined"), getObject(userroot_));
	return userroot_;
}
bool ClaspStatistics::removeStat(const StatisticObject& obj, bool recurse) {
	bool ret = impl_->remove(obj);
	if (ret && recurse) {
		if (obj.type() == Potassco::Statistics_t::Map) {
			for (uint32 i = 0, end = obj.size(); i != end; ++i) {
				removeStat(obj.at(obj.key(i)), true);
			}
		}
		else if (obj.type() == Potassco::Statistics_t::Array) {
			for (uint32 i = 0, end = obj.size(); i != end; ++i) {
				removeStat(obj[i], true);
			}
		}
	}
	return ret;
}
bool ClaspStatistics::removeStat(Key_t k, bool recurse) {
	try { return removeStat(impl_->get(k), recurse); }
	catch (const std::logic_error&) { return false; }
}
void ClaspStatistics::update() {
	if (root_) { impl_->update(getObject(root_)); }
}
StatisticObject ClaspStatistics::findObject(Key_t root, const char* path, Key_t* res) const {
	StatisticObject o = getObject(root);
	StatisticObject::Type t = o.type();
	char temp[1024]; const char* top, *parent = path;
	for (int pos; path && *path;) {
		top = path;
		if ((path = std::strchr(path, '.')) != 0) {
			std::size_t len = static_cast<std::size_t>(path++ - top);
			POTASSCO_ASSERT(len < 1024, "invalid key");
			top = (const char*)std::memcpy(temp, top, len);
			temp[len] = 0;
		}
		if      (t == Potassco::Statistics_t::Map) { o = o.at(top); }
		else if (t == Potassco::Statistics_t::Array && Potassco::match(top, pos) && pos >= 0) {
			o = o[uint32(pos)];
		}
		else {
			throw std::out_of_range(POTASSCO_FORMAT("invalid path: '%s' at key '%s'", parent, top));
		}
		t = o.type();
	}
	if (res) { *res = impl_->add(o); }
	return o;
}
StatisticObject ClaspStatistics::toUserStats() const {
	return StatisticObject::map(impl_->map(userroot_));
}

bool ClaspStatistics::userEmpty() const {
	return impl_->objects.size() <= 1;
}

StatisticObject StatsMap::at(const char* k) const {
	if (const StatisticObject* o = find(k)) { return *o; }
	throw std::out_of_range(POTASSCO_FORMAT("StatsMap::at with key '%s'", k));
}
const StatisticObject* StatsMap::find(const char* k) const {
	for (MapType::const_iterator it = keys_.begin(), end = keys_.end(); it != end; ++it) {
		if (std::strcmp(it->first, k) == 0) { return &it->second; }
	}
	return 0;
}
bool StatsMap::add(const char* k, const StatisticObject& o) {
	return !find(k) && (keys_.push_back(MapType::value_type(k, o)), true);
}
void StatsMap::push(const char* k, const StatisticObject& o) {
	keys_.push_back(MapType::value_type(k, o));
}
/////////////////////////////////////////////////////////////////////////////////////////
// StatsVisitor
/////////////////////////////////////////////////////////////////////////////////////////
StatsVisitor::~StatsVisitor() {}
bool StatsVisitor::visitGenerator(Operation) {
	return true;
}
bool StatsVisitor::visitThreads(Operation) {
	return true;
}
bool StatsVisitor::visitTester(Operation) {
	return true;
}
bool StatsVisitor::visitHccs(Operation) {
	return true;
}
void StatsVisitor::visitHcc(uint32, const ProblemStats& p, const SolverStats& s) {
	visitProblemStats(p);
	visitSolverStats(s);
}
void StatsVisitor::visitThread(uint32, const SolverStats& stats) {
	visitSolverStats(stats);
}






}

