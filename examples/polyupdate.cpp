#pragma once
#include <algorithm>
#include <functional>
#include <vector>
#include <unordered_set>
#include <string>
#include <unordered_map>

class Polyupdate {
public:
protected:
  int _var23;
  std::vector< int  > _var24;
public:
  inline Polyupdate() {
    _var23 = 0;
    _var24 = (std::vector< int  > ());
  }
  explicit inline Polyupdate(std::vector< int  > x, int s) {
    _var23 = s;
    _var24 = x;
  }
  Polyupdate(const Polyupdate& other) = delete;
  inline int  sm() {
    int _sum109 = 0;
    for (int _x110 : _var24) {
      _sum109 = (_sum109 + _x110);
    }
    return (_var23 + _sum109);
  }
  inline void a (int y) {
    int _conditional_result111 = 0;
    if ((y > 0)) {
      _conditional_result111 = (_var23 + y);
    } else {
      _conditional_result111 = _var23;
    }
    int _var91 = _conditional_result111;
    std::vector< int  > _var112 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram114 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x115 : _var24) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator124 = _histogram114.find(_x115);
      if ((_map_iterator124 == _histogram114.end())) {
        _map_iterator124 = (_histogram114.emplace(_x115, 0).first);
      }
      int &_count116 = _map_iterator124->second;

      _count116 = (_count116 + 1);
    }
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator125 = _histogram114.find(y);
      if ((_map_iterator125 == _histogram114.end())) {
        _map_iterator125 = (_histogram114.emplace(y, 0).first);
      }
      int &_count116 = _map_iterator125->second;

      _count116 = (_count116 + 1);
    }
    for (int _var113 : _var24) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator126 = (_histogram114.find(_var113));
      int _v127;
      if ((_map_iterator126 == _histogram114.end())) {
        _v127 = 0;
      } else {
        _v127 = (_map_iterator126->second);
      }
      if ((_v127 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator128 = _histogram114.find(_var113);
        if ((_map_iterator128 == _histogram114.end())) {
          _map_iterator128 = (_histogram114.emplace(_var113, 0).first);
        }
        int &_count117 = _map_iterator128->second;

        _count117 = (_count117 - 1);
      } else {
        _var112.push_back(_var113);
      }
    }
    std::vector< int  > _var92 = std::move(_var112);
    std::vector< int  > _var118 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram120 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x121 : _var24) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator129 = _histogram120.find(_x121);
      if ((_map_iterator129 == _histogram120.end())) {
        _map_iterator129 = (_histogram120.emplace(_x121, 0).first);
      }
      int &_count122 = _map_iterator129->second;

      _count122 = (_count122 + 1);
    }
    for (int _var119 : _var24) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator130 = (_histogram120.find(_var119));
      int _v131;
      if ((_map_iterator130 == _histogram120.end())) {
        _v131 = 0;
      } else {
        _v131 = (_map_iterator130->second);
      }
      if ((_v131 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator132 = _histogram120.find(_var119);
        if ((_map_iterator132 == _histogram120.end())) {
          _map_iterator132 = (_histogram120.emplace(_var119, 0).first);
        }
        int &_count123 = _map_iterator132->second;

        _count123 = (_count123 - 1);
      } else {
        _var118.push_back(_var119);
      }
    }
    {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator133 = (_histogram120.find(y));
      int _v134;
      if ((_map_iterator133 == _histogram120.end())) {
        _v134 = 0;
      } else {
        _v134 = (_map_iterator133->second);
      }
      if ((_v134 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator135 = _histogram120.find(y);
        if ((_map_iterator135 == _histogram120.end())) {
          _map_iterator135 = (_histogram120.emplace(y, 0).first);
        }
        int &_count123 = _map_iterator135->second;

        _count123 = (_count123 - 1);
      } else {
        _var118.push_back(y);
      }
    }
    std::vector< int  > _var93 = std::move(_var118);
    _var23 = _var91;
    for (int _var56 : _var92) {
      auto _it136(::std::find(_var24.begin(), _var24.end(), _var56));
      if (_it136 != _var24.end()) { _var24.erase(_it136); }
    }
    for (int _var56 : _var93) {
      _var24.push_back(_var56);
    }
  }
};
