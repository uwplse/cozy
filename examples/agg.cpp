#pragma once
#include <algorithm>
#include <functional>
#include <vector>
#include <unordered_set>
#include <string>
#include <unordered_map>

class Aggr {
public:
protected:
  std::vector< int  > _var33;
public:
  inline Aggr() {
    _var33 = (std::vector< int  > ());
  }
  explicit inline Aggr(std::vector< int  > l) {
    _var33 = l;
  }
  Aggr(const Aggr& other) = delete;
  template <class F>
  inline void elems(const F& _callback) {
    for (int _x112 : _var33) {
      _callback(_x112);
    }
  }
  inline int  totalSum() {
    int _sum113 = 0;
    for (int _i115 : _var33) {
      {
        _sum113 = (_sum113 + _i115);
      }
    }
    return _sum113;
  }
  inline int  countGt10() {
    int _sum116 = 0;
    for (int _x119 : _var33) {
      if ((_x119 > 10)) {
        {
          {
            _sum116 = (_sum116 + 1);
          }
        }
      }
    }
    return _sum116;
  }
  inline void add (int i) {
    std::vector< int  > _var120 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram122 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x123 : _var33) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator132 = _histogram122.find(_x123);
      if ((_map_iterator132 == _histogram122.end())) {
        _map_iterator132 = (_histogram122.emplace(_x123, 0).first);
      }
      int &_count124 = _map_iterator132->second;

      _count124 = (_count124 + 1);
    }
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator133 = _histogram122.find(i);
      if ((_map_iterator133 == _histogram122.end())) {
        _map_iterator133 = (_histogram122.emplace(i, 0).first);
      }
      int &_count124 = _map_iterator133->second;

      _count124 = (_count124 + 1);
    }
    for (int _var121 : _var33) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator134 = (_histogram122.find(_var121));
      int _v135;
      if ((_map_iterator134 == _histogram122.end())) {
        _v135 = 0;
      } else {
        _v135 = (_map_iterator134->second);
      }
      if ((_v135 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator136 = _histogram122.find(_var121);
        if ((_map_iterator136 == _histogram122.end())) {
          _map_iterator136 = (_histogram122.emplace(_var121, 0).first);
        }
        int &_count125 = _map_iterator136->second;

        _count125 = (_count125 - 1);
      } else {
        _var120.push_back(_var121);
      }
    }
    std::vector< int  > _var90 = std::move(_var120);
    std::vector< int  > _var126 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram128 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x129 : _var33) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator137 = _histogram128.find(_x129);
      if ((_map_iterator137 == _histogram128.end())) {
        _map_iterator137 = (_histogram128.emplace(_x129, 0).first);
      }
      int &_count130 = _map_iterator137->second;

      _count130 = (_count130 + 1);
    }
    for (int _var127 : _var33) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator138 = (_histogram128.find(_var127));
      int _v139;
      if ((_map_iterator138 == _histogram128.end())) {
        _v139 = 0;
      } else {
        _v139 = (_map_iterator138->second);
      }
      if ((_v139 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator140 = _histogram128.find(_var127);
        if ((_map_iterator140 == _histogram128.end())) {
          _map_iterator140 = (_histogram128.emplace(_var127, 0).first);
        }
        int &_count131 = _map_iterator140->second;

        _count131 = (_count131 - 1);
      } else {
        _var126.push_back(_var127);
      }
    }
    {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator141 = (_histogram128.find(i));
      int _v142;
      if ((_map_iterator141 == _histogram128.end())) {
        _v142 = 0;
      } else {
        _v142 = (_map_iterator141->second);
      }
      if ((_v142 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator143 = _histogram128.find(i);
        if ((_map_iterator143 == _histogram128.end())) {
          _map_iterator143 = (_histogram128.emplace(i, 0).first);
        }
        int &_count131 = _map_iterator143->second;

        _count131 = (_count131 - 1);
      } else {
        _var126.push_back(i);
      }
    }
    std::vector< int  > _var91 = std::move(_var126);
    for (int _var50 : _var90) {
      auto _it144(::std::find(_var33.begin(), _var33.end(), _var50));
      if (_it144 != _var33.end()) { _var33.erase(_it144); }
    }
    for (int _var50 : _var91) {
      _var33.push_back(_var50);
    }
  }
};
