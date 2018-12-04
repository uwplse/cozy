#pragma once
#include <algorithm>
#include <functional>
#include <vector>
#include <unordered_set>
#include <string>
#include <unordered_map>

class Map {
public:
protected:
  std::vector< int  > _var29;
public:
  inline Map() {
    _var29 = (std::vector< int  > ());
  }
  explicit inline Map(std::vector< int  > xs) {
    _var29 = xs;
  }
  Map(const Map& other) = delete;
  template <class F>
  inline void a(int z, const F& _callback) {
    for (int _x186 : _var29) {
      if (((_x186 == z))) {
        {
          {
            _callback(_x186);
          }
        }
      }
    }
  }
  inline void add (int x) {
    std::vector< int  > _var187 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram189 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x190 : _var29) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator199 = _histogram189.find(_x190);
      if ((_map_iterator199 == _histogram189.end())) {
        _map_iterator199 = (_histogram189.emplace(_x190, 0).first);
      }
      int &_count191 = _map_iterator199->second;

      _count191 = (_count191 + 1);
    }
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator200 = _histogram189.find(x);
      if ((_map_iterator200 == _histogram189.end())) {
        _map_iterator200 = (_histogram189.emplace(x, 0).first);
      }
      int &_count191 = _map_iterator200->second;

      _count191 = (_count191 + 1);
    }
    for (int _var188 : _var29) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator201 = (_histogram189.find(_var188));
      int _v202;
      if ((_map_iterator201 == _histogram189.end())) {
        _v202 = 0;
      } else {
        _v202 = (_map_iterator201->second);
      }
      if ((_v202 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator203 = _histogram189.find(_var188);
        if ((_map_iterator203 == _histogram189.end())) {
          _map_iterator203 = (_histogram189.emplace(_var188, 0).first);
        }
        int &_count192 = _map_iterator203->second;

        _count192 = (_count192 - 1);
      } else {
        _var187.push_back(_var188);
      }
    }
    std::vector< int  > _var145 = std::move(_var187);
    std::vector< int  > _var193 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram195 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x196 : _var29) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator204 = _histogram195.find(_x196);
      if ((_map_iterator204 == _histogram195.end())) {
        _map_iterator204 = (_histogram195.emplace(_x196, 0).first);
      }
      int &_count197 = _map_iterator204->second;

      _count197 = (_count197 + 1);
    }
    for (int _var194 : _var29) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator205 = (_histogram195.find(_var194));
      int _v206;
      if ((_map_iterator205 == _histogram195.end())) {
        _v206 = 0;
      } else {
        _v206 = (_map_iterator205->second);
      }
      if ((_v206 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator207 = _histogram195.find(_var194);
        if ((_map_iterator207 == _histogram195.end())) {
          _map_iterator207 = (_histogram195.emplace(_var194, 0).first);
        }
        int &_count198 = _map_iterator207->second;

        _count198 = (_count198 - 1);
      } else {
        _var193.push_back(_var194);
      }
    }
    {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator208 = (_histogram195.find(x));
      int _v209;
      if ((_map_iterator208 == _histogram195.end())) {
        _v209 = 0;
      } else {
        _v209 = (_map_iterator208->second);
      }
      if ((_v209 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator210 = _histogram195.find(x);
        if ((_map_iterator210 == _histogram195.end())) {
          _map_iterator210 = (_histogram195.emplace(x, 0).first);
        }
        int &_count198 = _map_iterator210->second;

        _count198 = (_count198 - 1);
      } else {
        _var193.push_back(x);
      }
    }
    std::vector< int  > _var146 = std::move(_var193);
    for (int _var46 : _var145) {
      auto _it211(::std::find(_var29.begin(), _var29.end(), _var46));
      if (_it211 != _var29.end()) { _var29.erase(_it211); }
    }
    for (int _var46 : _var146) {
      _var29.push_back(_var46);
    }
  }
  inline void rm (int x) {
    std::vector< int  > _var212 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram214 = (std::unordered_map< int , int , std::hash<int > > ());
    std::unordered_map< int , int , std::hash<int > > _histogram218 = (std::unordered_map< int , int , std::hash<int > > ());
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator232 = _histogram218.find(x);
      if ((_map_iterator232 == _histogram218.end())) {
        _map_iterator232 = (_histogram218.emplace(x, 0).first);
      }
      int &_count220 = _map_iterator232->second;

      _count220 = (_count220 + 1);
    }
    for (int _x215 : _var29) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator233 = (_histogram218.find(_x215));
      int _v234;
      if ((_map_iterator233 == _histogram218.end())) {
        _v234 = 0;
      } else {
        _v234 = (_map_iterator233->second);
      }
      if ((_v234 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator235 = _histogram218.find(_x215);
        if ((_map_iterator235 == _histogram218.end())) {
          _map_iterator235 = (_histogram218.emplace(_x215, 0).first);
        }
        int &_count221 = _map_iterator235->second;

        _count221 = (_count221 - 1);
      } else {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator236 = _histogram214.find(_x215);
        if ((_map_iterator236 == _histogram214.end())) {
          _map_iterator236 = (_histogram214.emplace(_x215, 0).first);
        }
        int &_count216 = _map_iterator236->second;

        _count216 = (_count216 + 1);
      }
    }
    for (int _var213 : _var29) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator237 = (_histogram214.find(_var213));
      int _v238;
      if ((_map_iterator237 == _histogram214.end())) {
        _v238 = 0;
      } else {
        _v238 = (_map_iterator237->second);
      }
      if ((_v238 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator239 = _histogram214.find(_var213);
        if ((_map_iterator239 == _histogram214.end())) {
          _map_iterator239 = (_histogram214.emplace(_var213, 0).first);
        }
        int &_count217 = _map_iterator239->second;

        _count217 = (_count217 - 1);
      } else {
        _var212.push_back(_var213);
      }
    }
    std::vector< int  > _var147 = std::move(_var212);
    std::vector< int  > _var222 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram224 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x225 : _var29) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator240 = _histogram224.find(_x225);
      if ((_map_iterator240 == _histogram224.end())) {
        _map_iterator240 = (_histogram224.emplace(_x225, 0).first);
      }
      int &_count226 = _map_iterator240->second;

      _count226 = (_count226 + 1);
    }
    std::unordered_map< int , int , std::hash<int > > _histogram228 = (std::unordered_map< int , int , std::hash<int > > ());
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator241 = _histogram228.find(x);
      if ((_map_iterator241 == _histogram228.end())) {
        _map_iterator241 = (_histogram228.emplace(x, 0).first);
      }
      int &_count230 = _map_iterator241->second;

      _count230 = (_count230 + 1);
    }
    for (int _var223 : _var29) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator242 = (_histogram228.find(_var223));
      int _v243;
      if ((_map_iterator242 == _histogram228.end())) {
        _v243 = 0;
      } else {
        _v243 = (_map_iterator242->second);
      }
      if ((_v243 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator244 = _histogram228.find(_var223);
        if ((_map_iterator244 == _histogram228.end())) {
          _map_iterator244 = (_histogram228.emplace(_var223, 0).first);
        }
        int &_count231 = _map_iterator244->second;

        _count231 = (_count231 - 1);
      } else {
        std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator245 = (_histogram224.find(_var223));
        int _v246;
        if ((_map_iterator245 == _histogram224.end())) {
          _v246 = 0;
        } else {
          _v246 = (_map_iterator245->second);
        }
        if ((_v246 > 0)) {
          std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator247 = _histogram224.find(_var223);
          if ((_map_iterator247 == _histogram224.end())) {
            _map_iterator247 = (_histogram224.emplace(_var223, 0).first);
          }
          int &_count227 = _map_iterator247->second;

          _count227 = (_count227 - 1);
        } else {
          _var222.push_back(_var223);
        }
      }
    }
    std::vector< int  > _var148 = std::move(_var222);
    for (int _var96 : _var147) {
      auto _it248(::std::find(_var29.begin(), _var29.end(), _var96));
      if (_it248 != _var29.end()) { _var29.erase(_it248); }
    }
    for (int _var96 : _var148) {
      _var29.push_back(_var96);
    }
  }
};
