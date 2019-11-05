#include "SelectMany.h"
#include <iostream>

void query(SelectFlatmap::_Type3508 elem) {
    std::cout << "Found elem(" << elem._0 << "," <<
        elem._1 << "," << elem._2 << "," << elem._3 << ")" << std::endl;
}

int main() {
    SelectMany::R r(15, "hello");   
    std::vector<SelectMany::R> Rs;
    Rs.push_back(r);

    SelectMany::W w("world", 100);
    std::vector<SelectMany::W> Ws;
    Ws.push_back(w);

    SelectMany m(Rs, Ws, Ws, Ws);
    m.q(query);
    return 0;
}
