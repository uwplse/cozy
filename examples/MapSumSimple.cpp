// listcomp example main driver
#include <iostream>

#include "MapSumSimple.h"

#include <chrono>

using namespace std::chrono;

constexpr int max_iter = 10000;

long now_ms() {
    milliseconds ms = duration_cast< milliseconds >(
        system_clock::now().time_since_epoch()
    );
    return ms.count();
}

int main(int argc, char const *argv[])
{
    MapSumSimple l;
    long initial_count = now_ms();
    for (int i = 0; i < max_iter; i++) {
        if (i % (max_iter / 100) == 0) {
            std::cout << i << " " << now_ms() - initial_count << std::endl;
        }
        l.insert_s(MapSumSimple::S("a", 2));
    }
    return 0;
}
