#pragma once
#include <algorithm>
#include <functional>
#include <vector>
#include <unordered_set>
#include <string>
#include <unordered_map>

class Structure {
public:
protected:
  int _var14;
public:
  inline Structure() {
    _var14 = 0;
  }
  explicit inline Structure(int x) {
    _var14 = x;
  }
  Structure(const Structure& other) = delete;
  inline int  foo() {
    return ((_var14) + 1);
  }
  inline void setX (int y) {
    _var14 = y;
  }
};
