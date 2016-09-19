#include <thread>
#include <atomic>
std::atomic<int> a;
void f() {
	a.fetch_sub(10);
}
int main() {
	a = 0;
	std::thread t(f);
	a.fetch_add(10);
	t.join();
	return !!a;
}
