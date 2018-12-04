#pragma once
#include <algorithm>
#include <functional>
#include <vector>
#include <unordered_set>
#include <string>
#include <unordered_map>

class BoundsBug2 {
public:
protected:
  bool _var14 : 1;
public:
  inline BoundsBug2() {
    _var14 = false;
  }
  explicit inline BoundsBug2(int executions, bool bugHappened) {
    _var14 = bugHappened;
  }
  BoundsBug2(const BoundsBug2& other) = delete;
  inline bool  didBugHappen() {
    return _var14;
  }
  inline void exec () {
  }
};
