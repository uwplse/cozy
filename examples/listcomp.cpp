// listcomp example main driver
#include <iostream>

#include "listcomp.h"

#include <chrono>

using namespace std::chrono;

constexpr int max_iter = 10000;

int main(int argc, char const *argv[])
{
    ListComp02 l;
    milliseconds ms = duration_cast< milliseconds >(
        system_clock::now().time_since_epoch()
    );
    long initial_count = ms.count();
    long total = 0;
    for (int i = 0; i <max_iter; i++) {
        if (i % (max_iter / 100) == 0) {
            milliseconds ms = duration_cast< milliseconds >(
                system_clock::now().time_since_epoch()
            );
            std::cout << i << " " << ms.count() - initial_count << " " << total << std::endl;
        }
        l.insert_r(ListComp02::R(1, ""));
        l.insert_s(ListComp02::S("a", 2));
        total += l.q();
    }
    return 0;
}
