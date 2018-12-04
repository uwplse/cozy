#pragma once
#include <algorithm>
#include <functional>
#include <vector>
#include <unordered_set>
#include <string>
#include <unordered_map>

class ReadAfterWrite {
public:
protected:
  int _var24;
  std::vector< int  > _var38;
public:
  inline ReadAfterWrite() {
    _var24 = 0;
    _var38 = (std::vector< int  > ());
  }
  explicit inline ReadAfterWrite(int x, std::vector< int  > l) {
    _var24 = x;
    _var38 = l;
  }
  ReadAfterWrite(const ReadAfterWrite& other) = delete;
  inline int  getx() {
    return _var24;
  }
  template <class F>
  inline void elems(const F& _callback) {
    for (int _x117 : _var38) {
      _callback(_x117);
    }
  }
  inline void do_thing (int n) {
    std::vector< int  > _var118 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram120 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x121 : _var38) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator130 = _histogram120.find(_x121);
      if ((_map_iterator130 == _histogram120.end())) {
        _map_iterator130 = (_histogram120.emplace(_x121, 0).first);
      }
      int &_count122 = _map_iterator130->second;

      _count122 = (_count122 + 1);
    }
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator131 = _histogram120.find((_var24 + n));
      if ((_map_iterator131 == _histogram120.end())) {
        _map_iterator131 = (_histogram120.emplace((_var24 + n), 0).first);
      }
      int &_count122 = _map_iterator131->second;

      _count122 = (_count122 + 1);
    }
    for (int _var119 : _var38) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator132 = (_histogram120.find(_var119));
      int _v133;
      if ((_map_iterator132 == _histogram120.end())) {
        _v133 = 0;
      } else {
        _v133 = (_map_iterator132->second);
      }
      if ((_v133 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator134 = _histogram120.find(_var119);
        if ((_map_iterator134 == _histogram120.end())) {
          _map_iterator134 = (_histogram120.emplace(_var119, 0).first);
        }
        int &_count123 = _map_iterator134->second;

        _count123 = (_count123 - 1);
      } else {
        _var118.push_back(_var119);
      }
    }
    std::vector< int  > _var101 = std::move(_var118);
    std::vector< int  > _var124 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram126 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x127 : _var38) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator135 = _histogram126.find(_x127);
      if ((_map_iterator135 == _histogram126.end())) {
        _map_iterator135 = (_histogram126.emplace(_x127, 0).first);
      }
      int &_count128 = _map_iterator135->second;

      _count128 = (_count128 + 1);
    }
    for (int _var125 : _var38) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator136 = (_histogram126.find(_var125));
      int _v137;
      if ((_map_iterator136 == _histogram126.end())) {
        _v137 = 0;
      } else {
        _v137 = (_map_iterator136->second);
      }
      if ((_v137 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator138 = _histogram126.find(_var125);
        if ((_map_iterator138 == _histogram126.end())) {
          _map_iterator138 = (_histogram126.emplace(_var125, 0).first);
        }
        int &_count129 = _map_iterator138->second;

        _count129 = (_count129 - 1);
      } else {
        _var124.push_back(_var125);
      }
    }
    {
      int _var125 = (_var24 + n);
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator139 = (_histogram126.find(_var125));
      int _v140;
      if ((_map_iterator139 == _histogram126.end())) {
        _v140 = 0;
      } else {
        _v140 = (_map_iterator139->second);
      }
      if ((_v140 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator141 = _histogram126.find(_var125);
        if ((_map_iterator141 == _histogram126.end())) {
          _map_iterator141 = (_histogram126.emplace(_var125, 0).first);
        }
        int &_count129 = _map_iterator141->second;

        _count129 = (_count129 - 1);
      } else {
        _var124.push_back(_var125);
      }
    }
    std::vector< int  > _var102 = std::move(_var124);
    int _var103 = (_var24 + n);
    for (int _var57 : _var101) {
      auto _it142(::std::find(_var38.begin(), _var38.end(), _var57));
      if (_it142 != _var38.end()) { _var38.erase(_it142); }
    }
    for (int _var57 : _var102) {
      _var38.push_back(_var57);
    }
    _var24 = _var103;
  }
};
