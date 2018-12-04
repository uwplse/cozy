#pragma once
#include <algorithm>
#include <functional>
#include <vector>
#include <unordered_set>
#include <string>
#include <unordered_map>

class In {
public:
protected:
  std::vector< int  > _var34;
public:
  inline In() {
    _var34 = (std::vector< int  > ());
  }
  explicit inline In(std::vector< int  > xs, std::vector< int  > ys) {
    _var34 = ys;
  }
  In(const In& other) = delete;
  inline bool  a(int z) {
    bool _found126 = false;
    {
      for (int _x127 : _var34) {
        if (((_x127 == z))) {
          _found126 = true;
          goto _label129;
        }
      }
    }
_label129:
    return _found126;
  }
  inline void addX (int x) {
  }
  inline void addY (int y) {
    std::vector< int  > _var130 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram132 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x133 : _var34) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator142 = _histogram132.find(_x133);
      if ((_map_iterator142 == _histogram132.end())) {
        _map_iterator142 = (_histogram132.emplace(_x133, 0).first);
      }
      int &_count134 = _map_iterator142->second;

      _count134 = (_count134 + 1);
    }
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator143 = _histogram132.find(y);
      if ((_map_iterator143 == _histogram132.end())) {
        _map_iterator143 = (_histogram132.emplace(y, 0).first);
      }
      int &_count134 = _map_iterator143->second;

      _count134 = (_count134 + 1);
    }
    for (int _var131 : _var34) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator144 = (_histogram132.find(_var131));
      int _v145;
      if ((_map_iterator144 == _histogram132.end())) {
        _v145 = 0;
      } else {
        _v145 = (_map_iterator144->second);
      }
      if ((_v145 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator146 = _histogram132.find(_var131);
        if ((_map_iterator146 == _histogram132.end())) {
          _map_iterator146 = (_histogram132.emplace(_var131, 0).first);
        }
        int &_count135 = _map_iterator146->second;

        _count135 = (_count135 - 1);
      } else {
        _var130.push_back(_var131);
      }
    }
    std::vector< int  > _var109 = std::move(_var130);
    std::vector< int  > _var136 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram138 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x139 : _var34) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator147 = _histogram138.find(_x139);
      if ((_map_iterator147 == _histogram138.end())) {
        _map_iterator147 = (_histogram138.emplace(_x139, 0).first);
      }
      int &_count140 = _map_iterator147->second;

      _count140 = (_count140 + 1);
    }
    for (int _var137 : _var34) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator148 = (_histogram138.find(_var137));
      int _v149;
      if ((_map_iterator148 == _histogram138.end())) {
        _v149 = 0;
      } else {
        _v149 = (_map_iterator148->second);
      }
      if ((_v149 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator150 = _histogram138.find(_var137);
        if ((_map_iterator150 == _histogram138.end())) {
          _map_iterator150 = (_histogram138.emplace(_var137, 0).first);
        }
        int &_count141 = _map_iterator150->second;

        _count141 = (_count141 - 1);
      } else {
        _var136.push_back(_var137);
      }
    }
    {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator151 = (_histogram138.find(y));
      int _v152;
      if ((_map_iterator151 == _histogram138.end())) {
        _v152 = 0;
      } else {
        _v152 = (_map_iterator151->second);
      }
      if ((_v152 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator153 = _histogram138.find(y);
        if ((_map_iterator153 == _histogram138.end())) {
          _map_iterator153 = (_histogram138.emplace(y, 0).first);
        }
        int &_count141 = _map_iterator153->second;

        _count141 = (_count141 - 1);
      } else {
        _var136.push_back(y);
      }
    }
    std::vector< int  > _var110 = std::move(_var136);
    for (int _var62 : _var109) {
      auto _it154(::std::find(_var34.begin(), _var34.end(), _var62));
      if (_it154 != _var34.end()) { _var34.erase(_it154); }
    }
    for (int _var62 : _var110) {
      _var34.push_back(_var62);
    }
  }
};
