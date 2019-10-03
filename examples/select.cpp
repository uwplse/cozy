#include "select.h"
#include <iostream>

void query(SelectFlatmap::_Type3508 elem) {
    std::cout << "Found elem(" << elem._0 << "," <<
        elem._1 << "," << elem._2 << "," << elem._3 << ")" << std::endl;
}

int main() {
    SelectFlatmap::R r(15, "hello");
    std::vector<SelectFlatmap::R> Rs;
    Rs.push_back(r);

    SelectFlatmap::W w("world", 100);
    std::vector<SelectFlatmap::W> Ws;
    Ws.push_back(w);

    SelectFlatmap m(Rs, Ws, Ws, Ws);
    m.q(query);
    return 0;
}