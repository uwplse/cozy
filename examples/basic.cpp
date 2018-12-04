#pragma once
#include <algorithm>
#include <functional>
#include <vector>
#include <unordered_set>
#include <string>
#include <unordered_map>

class Basic {
public:
protected:
  std::vector< int  > _var23;
public:
  inline Basic() {
    _var23 = (std::vector< int  > ());
  }
  explicit inline Basic(std::vector< int  > l) {
    _var23 = l;
  }
  Basic(const Basic& other) = delete;
  template <class F>
  inline void elems(const F& _callback) {
    for (int _x165 : _var23) {
      _callback(_x165);
    }
  }
  inline void add (int n) {
    std::vector< int  > _var166 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram168 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x169 : _var23) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator178 = _histogram168.find(_x169);
      if ((_map_iterator178 == _histogram168.end())) {
        _map_iterator178 = (_histogram168.emplace(_x169, 0).first);
      }
      int &_count170 = _map_iterator178->second;

      _count170 = (_count170 + 1);
    }
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator179 = _histogram168.find(n);
      if ((_map_iterator179 == _histogram168.end())) {
        _map_iterator179 = (_histogram168.emplace(n, 0).first);
      }
      int &_count170 = _map_iterator179->second;

      _count170 = (_count170 + 1);
    }
    for (int _var167 : _var23) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator180 = (_histogram168.find(_var167));
      int _v181;
      if ((_map_iterator180 == _histogram168.end())) {
        _v181 = 0;
      } else {
        _v181 = (_map_iterator180->second);
      }
      if ((_v181 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator182 = _histogram168.find(_var167);
        if ((_map_iterator182 == _histogram168.end())) {
          _map_iterator182 = (_histogram168.emplace(_var167, 0).first);
        }
        int &_count171 = _map_iterator182->second;

        _count171 = (_count171 - 1);
      } else {
        _var166.push_back(_var167);
      }
    }
    std::vector< int  > _var132 = std::move(_var166);
    std::vector< int  > _var172 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram174 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x175 : _var23) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator183 = _histogram174.find(_x175);
      if ((_map_iterator183 == _histogram174.end())) {
        _map_iterator183 = (_histogram174.emplace(_x175, 0).first);
      }
      int &_count176 = _map_iterator183->second;

      _count176 = (_count176 + 1);
    }
    for (int _var173 : _var23) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator184 = (_histogram174.find(_var173));
      int _v185;
      if ((_map_iterator184 == _histogram174.end())) {
        _v185 = 0;
      } else {
        _v185 = (_map_iterator184->second);
      }
      if ((_v185 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator186 = _histogram174.find(_var173);
        if ((_map_iterator186 == _histogram174.end())) {
          _map_iterator186 = (_histogram174.emplace(_var173, 0).first);
        }
        int &_count177 = _map_iterator186->second;

        _count177 = (_count177 - 1);
      } else {
        _var172.push_back(_var173);
      }
    }
    {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator187 = (_histogram174.find(n));
      int _v188;
      if ((_map_iterator187 == _histogram174.end())) {
        _v188 = 0;
      } else {
        _v188 = (_map_iterator187->second);
      }
      if ((_v188 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator189 = _histogram174.find(n);
        if ((_map_iterator189 == _histogram174.end())) {
          _map_iterator189 = (_histogram174.emplace(n, 0).first);
        }
        int &_count177 = _map_iterator189->second;

        _count177 = (_count177 - 1);
      } else {
        _var172.push_back(n);
      }
    }
    std::vector< int  > _var133 = std::move(_var172);
    for (int _var40 : _var132) {
      auto _it190(::std::find(_var23.begin(), _var23.end(), _var40));
      if (_it190 != _var23.end()) { _var23.erase(_it190); }
    }
    for (int _var40 : _var133) {
      _var23.push_back(_var40);
    }
  }
  inline void remove (int n) {
    std::vector< int  > _var191 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram193 = (std::unordered_map< int , int , std::hash<int > > ());
    std::unordered_map< int , int , std::hash<int > > _histogram197 = (std::unordered_map< int , int , std::hash<int > > ());
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator207 = _histogram197.find(n);
      if ((_map_iterator207 == _histogram197.end())) {
        _map_iterator207 = (_histogram197.emplace(n, 0).first);
      }
      int &_count199 = _map_iterator207->second;

      _count199 = (_count199 + 1);
    }
    for (int _x194 : _var23) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator208 = (_histogram197.find(_x194));
      int _v209;
      if ((_map_iterator208 == _histogram197.end())) {
        _v209 = 0;
      } else {
        _v209 = (_map_iterator208->second);
      }
      if ((_v209 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator210 = _histogram197.find(_x194);
        if ((_map_iterator210 == _histogram197.end())) {
          _map_iterator210 = (_histogram197.emplace(_x194, 0).first);
        }
        int &_count200 = _map_iterator210->second;

        _count200 = (_count200 - 1);
      } else {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator211 = _histogram193.find(_x194);
        if ((_map_iterator211 == _histogram193.end())) {
          _map_iterator211 = (_histogram193.emplace(_x194, 0).first);
        }
        int &_count195 = _map_iterator211->second;

        _count195 = (_count195 + 1);
      }
    }
    for (int _var192 : _var23) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator212 = (_histogram193.find(_var192));
      int _v213;
      if ((_map_iterator212 == _histogram193.end())) {
        _v213 = 0;
      } else {
        _v213 = (_map_iterator212->second);
      }
      if ((_v213 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator214 = _histogram193.find(_var192);
        if ((_map_iterator214 == _histogram193.end())) {
          _map_iterator214 = (_histogram193.emplace(_var192, 0).first);
        }
        int &_count196 = _map_iterator214->second;

        _count196 = (_count196 - 1);
      } else {
        _var191.push_back(_var192);
      }
    }
    std::vector< int  > _var134 = std::move(_var191);
    std::vector< int  > _var201 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram203 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x204 : _var23) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator215 = _histogram203.find(_x204);
      if ((_map_iterator215 == _histogram203.end())) {
        _map_iterator215 = (_histogram203.emplace(_x204, 0).first);
      }
      int &_count205 = _map_iterator215->second;

      _count205 = (_count205 + 1);
    }
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator216 = _histogram203.find(n);
      if ((_map_iterator216 == _histogram203.end())) {
        _map_iterator216 = (_histogram203.emplace(n, 0).first);
      }
      int &_count205 = _map_iterator216->second;

      _count205 = (_count205 + 1);
    }
    for (int _var202 : _var23) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator217 = (_histogram203.find(_var202));
      int _v218;
      if ((_map_iterator217 == _histogram203.end())) {
        _v218 = 0;
      } else {
        _v218 = (_map_iterator217->second);
      }
      if ((_v218 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator219 = _histogram203.find(_var202);
        if ((_map_iterator219 == _histogram203.end())) {
          _map_iterator219 = (_histogram203.emplace(_var202, 0).first);
        }
        int &_count206 = _map_iterator219->second;

        _count206 = (_count206 - 1);
      } else {
        _var201.push_back(_var202);
      }
    }
    std::vector< int  > _var135 = std::move(_var201);
    for (int _var89 : _var134) {
      auto _it220(::std::find(_var23.begin(), _var23.end(), _var89));
      if (_it220 != _var23.end()) { _var23.erase(_it220); }
    }
    for (int _var89 : _var135) {
      _var23.push_back(_var89);
    }
  }
};
