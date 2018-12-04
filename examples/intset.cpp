#pragma once
#include <algorithm>
#include <functional>
#include <vector>
#include <unordered_set>
#include <string>
#include <unordered_map>

class ClauseDB {
public:
protected:
  std::vector< int  > _var58;
public:
  inline ClauseDB() {
    _var58 = (std::vector< int  > ());
  }
  explicit inline ClauseDB(std::vector< int  > ints) {
    _var58 = ints;
  }
  ClauseDB(const ClauseDB& other) = delete;
  inline bool  contains(int i) {
    bool _found223 = false;
    {
      for (int _x224 : _var58) {
        if (((_x224 == i))) {
          _found223 = true;
          goto _label226;
        }
      }
    }
_label226:
    return _found223;
  }
  inline int  size() {
    int _sum227 = 0;
    for (int _x229 : _var58) {
      {
        _sum227 = (_sum227 + 1);
      }
    }
    return _sum227;
  }
  inline void add (int i) {
    std::vector< int  > _var230 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram232 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x233 : _var58) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator242 = _histogram232.find(_x233);
      if ((_map_iterator242 == _histogram232.end())) {
        _map_iterator242 = (_histogram232.emplace(_x233, 0).first);
      }
      int &_count234 = _map_iterator242->second;

      _count234 = (_count234 + 1);
    }
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator243 = _histogram232.find(i);
      if ((_map_iterator243 == _histogram232.end())) {
        _map_iterator243 = (_histogram232.emplace(i, 0).first);
      }
      int &_count234 = _map_iterator243->second;

      _count234 = (_count234 + 1);
    }
    for (int _var231 : _var58) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator244 = (_histogram232.find(_var231));
      int _v245;
      if ((_map_iterator244 == _histogram232.end())) {
        _v245 = 0;
      } else {
        _v245 = (_map_iterator244->second);
      }
      if ((_v245 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator246 = _histogram232.find(_var231);
        if ((_map_iterator246 == _histogram232.end())) {
          _map_iterator246 = (_histogram232.emplace(_var231, 0).first);
        }
        int &_count235 = _map_iterator246->second;

        _count235 = (_count235 - 1);
      } else {
        _var230.push_back(_var231);
      }
    }
    std::vector< int  > _var181 = std::move(_var230);
    std::vector< int  > _var236 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram238 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x239 : _var58) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator247 = _histogram238.find(_x239);
      if ((_map_iterator247 == _histogram238.end())) {
        _map_iterator247 = (_histogram238.emplace(_x239, 0).first);
      }
      int &_count240 = _map_iterator247->second;

      _count240 = (_count240 + 1);
    }
    for (int _var237 : _var58) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator248 = (_histogram238.find(_var237));
      int _v249;
      if ((_map_iterator248 == _histogram238.end())) {
        _v249 = 0;
      } else {
        _v249 = (_map_iterator248->second);
      }
      if ((_v249 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator250 = _histogram238.find(_var237);
        if ((_map_iterator250 == _histogram238.end())) {
          _map_iterator250 = (_histogram238.emplace(_var237, 0).first);
        }
        int &_count241 = _map_iterator250->second;

        _count241 = (_count241 - 1);
      } else {
        _var236.push_back(_var237);
      }
    }
    {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator251 = (_histogram238.find(i));
      int _v252;
      if ((_map_iterator251 == _histogram238.end())) {
        _v252 = 0;
      } else {
        _v252 = (_map_iterator251->second);
      }
      if ((_v252 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator253 = _histogram238.find(i);
        if ((_map_iterator253 == _histogram238.end())) {
          _map_iterator253 = (_histogram238.emplace(i, 0).first);
        }
        int &_count241 = _map_iterator253->second;

        _count241 = (_count241 - 1);
      } else {
        _var236.push_back(i);
      }
    }
    std::vector< int  > _var182 = std::move(_var236);
    for (int _var79 : _var181) {
      auto _it254(::std::find(_var58.begin(), _var58.end(), _var79));
      if (_it254 != _var58.end()) { _var58.erase(_it254); }
    }
    for (int _var79 : _var182) {
      _var58.push_back(_var79);
    }
  }
  inline void remove (int i) {
    std::vector< int  > _var255 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram257 = (std::unordered_map< int , int , std::hash<int > > ());
    std::unordered_map< int , int , std::hash<int > > _histogram261 = (std::unordered_map< int , int , std::hash<int > > ());
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator275 = _histogram261.find(i);
      if ((_map_iterator275 == _histogram261.end())) {
        _map_iterator275 = (_histogram261.emplace(i, 0).first);
      }
      int &_count263 = _map_iterator275->second;

      _count263 = (_count263 + 1);
    }
    for (int _x258 : _var58) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator276 = (_histogram261.find(_x258));
      int _v277;
      if ((_map_iterator276 == _histogram261.end())) {
        _v277 = 0;
      } else {
        _v277 = (_map_iterator276->second);
      }
      if ((_v277 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator278 = _histogram261.find(_x258);
        if ((_map_iterator278 == _histogram261.end())) {
          _map_iterator278 = (_histogram261.emplace(_x258, 0).first);
        }
        int &_count264 = _map_iterator278->second;

        _count264 = (_count264 - 1);
      } else {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator279 = _histogram257.find(_x258);
        if ((_map_iterator279 == _histogram257.end())) {
          _map_iterator279 = (_histogram257.emplace(_x258, 0).first);
        }
        int &_count259 = _map_iterator279->second;

        _count259 = (_count259 + 1);
      }
    }
    for (int _var256 : _var58) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator280 = (_histogram257.find(_var256));
      int _v281;
      if ((_map_iterator280 == _histogram257.end())) {
        _v281 = 0;
      } else {
        _v281 = (_map_iterator280->second);
      }
      if ((_v281 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator282 = _histogram257.find(_var256);
        if ((_map_iterator282 == _histogram257.end())) {
          _map_iterator282 = (_histogram257.emplace(_var256, 0).first);
        }
        int &_count260 = _map_iterator282->second;

        _count260 = (_count260 - 1);
      } else {
        _var255.push_back(_var256);
      }
    }
    std::vector< int  > _var183 = std::move(_var255);
    std::vector< int  > _var265 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram267 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x268 : _var58) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator283 = _histogram267.find(_x268);
      if ((_map_iterator283 == _histogram267.end())) {
        _map_iterator283 = (_histogram267.emplace(_x268, 0).first);
      }
      int &_count269 = _map_iterator283->second;

      _count269 = (_count269 + 1);
    }
    std::unordered_map< int , int , std::hash<int > > _histogram271 = (std::unordered_map< int , int , std::hash<int > > ());
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator284 = _histogram271.find(i);
      if ((_map_iterator284 == _histogram271.end())) {
        _map_iterator284 = (_histogram271.emplace(i, 0).first);
      }
      int &_count273 = _map_iterator284->second;

      _count273 = (_count273 + 1);
    }
    for (int _var266 : _var58) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator285 = (_histogram271.find(_var266));
      int _v286;
      if ((_map_iterator285 == _histogram271.end())) {
        _v286 = 0;
      } else {
        _v286 = (_map_iterator285->second);
      }
      if ((_v286 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator287 = _histogram271.find(_var266);
        if ((_map_iterator287 == _histogram271.end())) {
          _map_iterator287 = (_histogram271.emplace(_var266, 0).first);
        }
        int &_count274 = _map_iterator287->second;

        _count274 = (_count274 - 1);
      } else {
        std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator288 = (_histogram267.find(_var266));
        int _v289;
        if ((_map_iterator288 == _histogram267.end())) {
          _v289 = 0;
        } else {
          _v289 = (_map_iterator288->second);
        }
        if ((_v289 > 0)) {
          std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator290 = _histogram267.find(_var266);
          if ((_map_iterator290 == _histogram267.end())) {
            _map_iterator290 = (_histogram267.emplace(_var266, 0).first);
          }
          int &_count270 = _map_iterator290->second;

          _count270 = (_count270 - 1);
        } else {
          _var265.push_back(_var266);
        }
      }
    }
    std::vector< int  > _var184 = std::move(_var265);
    for (int _var156 : _var183) {
      auto _it291(::std::find(_var58.begin(), _var58.end(), _var156));
      if (_it291 != _var58.end()) { _var58.erase(_it291); }
    }
    for (int _var156 : _var184) {
      _var58.push_back(_var156);
    }
  }
};
