#pragma once
#include <algorithm>
#include <functional>
#include <vector>
#include <unordered_set>
#include <string>
#include <unordered_map>

class MaxBag {
public:
protected:
  std::vector< int  > _var73;
public:
  inline MaxBag() {
    _var73 = (std::vector< int  > ());
  }
  explicit inline MaxBag(std::vector< int  > l) {
    _var73 = l;
  }
  MaxBag(const MaxBag& other) = delete;
  inline int  get_max() {
    int _max233 = 0;
    bool _first234 = true;
    for (int _x235 : _var73) {
      bool _v236;
      if (_first234) {
        _v236 = true;
      } else {
        _v236 = (_x235 > _max233);
      }
      if (_v236) {
        _first234 = false;
        _max233 = _x235;
      }
    }
    return _max233;
  }
  inline void add (int x) {
    std::vector< int  > _var237 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram239 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x240 : _var73) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator249 = _histogram239.find(_x240);
      if ((_map_iterator249 == _histogram239.end())) {
        _map_iterator249 = (_histogram239.emplace(_x240, 0).first);
      }
      int &_count241 = _map_iterator249->second;

      _count241 = (_count241 + 1);
    }
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator250 = _histogram239.find(x);
      if ((_map_iterator250 == _histogram239.end())) {
        _map_iterator250 = (_histogram239.emplace(x, 0).first);
      }
      int &_count241 = _map_iterator250->second;

      _count241 = (_count241 + 1);
    }
    for (int _var238 : _var73) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator251 = (_histogram239.find(_var238));
      int _v252;
      if ((_map_iterator251 == _histogram239.end())) {
        _v252 = 0;
      } else {
        _v252 = (_map_iterator251->second);
      }
      if ((_v252 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator253 = _histogram239.find(_var238);
        if ((_map_iterator253 == _histogram239.end())) {
          _map_iterator253 = (_histogram239.emplace(_var238, 0).first);
        }
        int &_count242 = _map_iterator253->second;

        _count242 = (_count242 - 1);
      } else {
        _var237.push_back(_var238);
      }
    }
    std::vector< int  > _var193 = std::move(_var237);
    std::vector< int  > _var243 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram245 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x246 : _var73) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator254 = _histogram245.find(_x246);
      if ((_map_iterator254 == _histogram245.end())) {
        _map_iterator254 = (_histogram245.emplace(_x246, 0).first);
      }
      int &_count247 = _map_iterator254->second;

      _count247 = (_count247 + 1);
    }
    for (int _var244 : _var73) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator255 = (_histogram245.find(_var244));
      int _v256;
      if ((_map_iterator255 == _histogram245.end())) {
        _v256 = 0;
      } else {
        _v256 = (_map_iterator255->second);
      }
      if ((_v256 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator257 = _histogram245.find(_var244);
        if ((_map_iterator257 == _histogram245.end())) {
          _map_iterator257 = (_histogram245.emplace(_var244, 0).first);
        }
        int &_count248 = _map_iterator257->second;

        _count248 = (_count248 - 1);
      } else {
        _var243.push_back(_var244);
      }
    }
    {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator258 = (_histogram245.find(x));
      int _v259;
      if ((_map_iterator258 == _histogram245.end())) {
        _v259 = 0;
      } else {
        _v259 = (_map_iterator258->second);
      }
      if ((_v259 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator260 = _histogram245.find(x);
        if ((_map_iterator260 == _histogram245.end())) {
          _map_iterator260 = (_histogram245.emplace(x, 0).first);
        }
        int &_count248 = _map_iterator260->second;

        _count248 = (_count248 - 1);
      } else {
        _var243.push_back(x);
      }
    }
    std::vector< int  > _var194 = std::move(_var243);
    for (int _var94 : _var193) {
      auto _it261(::std::find(_var73.begin(), _var73.end(), _var94));
      if (_it261 != _var73.end()) { _var73.erase(_it261); }
    }
    for (int _var94 : _var194) {
      _var73.push_back(_var94);
    }
  }
  inline void remove (int x) {
    std::vector< int  > _var262 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram264 = (std::unordered_map< int , int , std::hash<int > > ());
    std::unordered_map< int , int , std::hash<int > > _histogram268 = (std::unordered_map< int , int , std::hash<int > > ());
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator282 = _histogram268.find(x);
      if ((_map_iterator282 == _histogram268.end())) {
        _map_iterator282 = (_histogram268.emplace(x, 0).first);
      }
      int &_count270 = _map_iterator282->second;

      _count270 = (_count270 + 1);
    }
    for (int _x265 : _var73) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator283 = (_histogram268.find(_x265));
      int _v284;
      if ((_map_iterator283 == _histogram268.end())) {
        _v284 = 0;
      } else {
        _v284 = (_map_iterator283->second);
      }
      if ((_v284 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator285 = _histogram268.find(_x265);
        if ((_map_iterator285 == _histogram268.end())) {
          _map_iterator285 = (_histogram268.emplace(_x265, 0).first);
        }
        int &_count271 = _map_iterator285->second;

        _count271 = (_count271 - 1);
      } else {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator286 = _histogram264.find(_x265);
        if ((_map_iterator286 == _histogram264.end())) {
          _map_iterator286 = (_histogram264.emplace(_x265, 0).first);
        }
        int &_count266 = _map_iterator286->second;

        _count266 = (_count266 + 1);
      }
    }
    for (int _var263 : _var73) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator287 = (_histogram264.find(_var263));
      int _v288;
      if ((_map_iterator287 == _histogram264.end())) {
        _v288 = 0;
      } else {
        _v288 = (_map_iterator287->second);
      }
      if ((_v288 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator289 = _histogram264.find(_var263);
        if ((_map_iterator289 == _histogram264.end())) {
          _map_iterator289 = (_histogram264.emplace(_var263, 0).first);
        }
        int &_count267 = _map_iterator289->second;

        _count267 = (_count267 - 1);
      } else {
        _var262.push_back(_var263);
      }
    }
    std::vector< int  > _var195 = std::move(_var262);
    std::vector< int  > _var272 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram274 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x275 : _var73) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator290 = _histogram274.find(_x275);
      if ((_map_iterator290 == _histogram274.end())) {
        _map_iterator290 = (_histogram274.emplace(_x275, 0).first);
      }
      int &_count276 = _map_iterator290->second;

      _count276 = (_count276 + 1);
    }
    std::unordered_map< int , int , std::hash<int > > _histogram278 = (std::unordered_map< int , int , std::hash<int > > ());
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator291 = _histogram278.find(x);
      if ((_map_iterator291 == _histogram278.end())) {
        _map_iterator291 = (_histogram278.emplace(x, 0).first);
      }
      int &_count280 = _map_iterator291->second;

      _count280 = (_count280 + 1);
    }
    for (int _var273 : _var73) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator292 = (_histogram278.find(_var273));
      int _v293;
      if ((_map_iterator292 == _histogram278.end())) {
        _v293 = 0;
      } else {
        _v293 = (_map_iterator292->second);
      }
      if ((_v293 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator294 = _histogram278.find(_var273);
        if ((_map_iterator294 == _histogram278.end())) {
          _map_iterator294 = (_histogram278.emplace(_var273, 0).first);
        }
        int &_count281 = _map_iterator294->second;

        _count281 = (_count281 - 1);
      } else {
        std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator295 = (_histogram274.find(_var273));
        int _v296;
        if ((_map_iterator295 == _histogram274.end())) {
          _v296 = 0;
        } else {
          _v296 = (_map_iterator295->second);
        }
        if ((_v296 > 0)) {
          std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator297 = _histogram274.find(_var273);
          if ((_map_iterator297 == _histogram274.end())) {
            _map_iterator297 = (_histogram274.emplace(_var273, 0).first);
          }
          int &_count277 = _map_iterator297->second;

          _count277 = (_count277 - 1);
        } else {
          _var272.push_back(_var273);
        }
      }
    }
    std::vector< int  > _var196 = std::move(_var272);
    for (int _var171 : _var195) {
      auto _it298(::std::find(_var73.begin(), _var73.end(), _var171));
      if (_it298 != _var73.end()) { _var73.erase(_it298); }
    }
    for (int _var171 : _var196) {
      _var73.push_back(_var171);
    }
  }
};
