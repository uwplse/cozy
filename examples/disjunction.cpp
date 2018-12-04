#pragma once
#include <algorithm>
#include <functional>
#include <vector>
#include <unordered_set>
#include <string>
#include <unordered_map>

class In {
public:
  struct _Type518 {
    int _0;
    int _1;
    inline _Type518() { }
    inline _Type518(int __0, int __1) : _0(::std::move(__0)), _1(::std::move(__1)) { }
    inline bool operator==(const _Type518& other) const {
      bool _v520;
      if (((((*this)._0) == (other._0)))) {
        _v520 = ((((*this)._1) == (other._1)));
      } else {
        _v520 = false;
      }
      return _v520;
    }
  };
  struct _Hash_Type518 {
    typedef In::_Type518 argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code521 = 0;
      int _hash_code522 = 0;
      _hash_code522 = (std::hash<int >()((x._0)));
      _hash_code521 = ((_hash_code521 * 31) ^ (_hash_code522));
      _hash_code522 = (std::hash<int >()((x._1)));
      _hash_code521 = ((_hash_code521 * 31) ^ (_hash_code522));
      return _hash_code521;
    }
  };
  struct Elem {
  public:
    _Type518 val;
  private:
  };
  protected:
  std::vector< Elem * > _var116;
public:
  inline In() {
    _var116 = (std::vector< Elem * > ());
  }
  explicit inline In(std::vector< Elem * > xs) {
    _var116 = xs;
  }
  In(const In& other) = delete;
  template <class F>
  inline void a(int st, int ed, const F& _callback) {
    for (Elem *_x525 : _var116) {
      bool _v526;
      _Type518 _v527;
      if (((_x525 == nullptr))) {
        _v527 = (_Type518(0, 0));
      } else {
        _v527 = (_x525->val);
      }
      if ((((_v527._0) == st))) {
        _v526 = true;
      } else {
        _Type518 _v528;
        if (((_x525 == nullptr))) {
          _v528 = (_Type518(0, 0));
        } else {
          _v528 = (_x525->val);
        }
        _v526 = (((_v528._1) == ed));
      }
      if (_v526) {
        {
          {
            _callback(_x525);
          }
        }
      }
    }
  }
  inline void add (Elem *e) {
    std::vector< Elem * > _var529 = (std::vector< Elem * > ());
    std::unordered_map< Elem *, int , std::hash<Elem *> > _histogram531 = (std::unordered_map< Elem *, int , std::hash<Elem *> > ());
    for (Elem *_x532 : _var116) {
      std::unordered_map< Elem *, int , std::hash<Elem *> >::iterator _map_iterator541 = _histogram531.find(_x532);
      if ((_map_iterator541 == _histogram531.end())) {
        _map_iterator541 = (_histogram531.emplace(_x532, 0).first);
      }
      int &_count533 = _map_iterator541->second;

      _count533 = (_count533 + 1);
    }
    {
      std::unordered_map< Elem *, int , std::hash<Elem *> >::iterator _map_iterator542 = _histogram531.find(e);
      if ((_map_iterator542 == _histogram531.end())) {
        _map_iterator542 = (_histogram531.emplace(e, 0).first);
      }
      int &_count533 = _map_iterator542->second;

      _count533 = (_count533 + 1);
    }
    for (Elem *_var530 : _var116) {
      std::unordered_map< Elem *, int , std::hash<Elem *> >::const_iterator _map_iterator543 = (_histogram531.find(_var530));
      int _v544;
      if ((_map_iterator543 == _histogram531.end())) {
        _v544 = 0;
      } else {
        _v544 = (_map_iterator543->second);
      }
      if ((_v544 > 0)) {
        std::unordered_map< Elem *, int , std::hash<Elem *> >::iterator _map_iterator545 = _histogram531.find(_var530);
        if ((_map_iterator545 == _histogram531.end())) {
          _map_iterator545 = (_histogram531.emplace(_var530, 0).first);
        }
        int &_count534 = _map_iterator545->second;

        _count534 = (_count534 - 1);
      } else {
        _var529.push_back(_var530);
      }
    }
    std::vector< Elem * > _var494 = std::move(_var529);
    std::vector< Elem * > _var535 = (std::vector< Elem * > ());
    std::unordered_map< Elem *, int , std::hash<Elem *> > _histogram537 = (std::unordered_map< Elem *, int , std::hash<Elem *> > ());
    for (Elem *_x538 : _var116) {
      std::unordered_map< Elem *, int , std::hash<Elem *> >::iterator _map_iterator546 = _histogram537.find(_x538);
      if ((_map_iterator546 == _histogram537.end())) {
        _map_iterator546 = (_histogram537.emplace(_x538, 0).first);
      }
      int &_count539 = _map_iterator546->second;

      _count539 = (_count539 + 1);
    }
    for (Elem *_var536 : _var116) {
      std::unordered_map< Elem *, int , std::hash<Elem *> >::const_iterator _map_iterator547 = (_histogram537.find(_var536));
      int _v548;
      if ((_map_iterator547 == _histogram537.end())) {
        _v548 = 0;
      } else {
        _v548 = (_map_iterator547->second);
      }
      if ((_v548 > 0)) {
        std::unordered_map< Elem *, int , std::hash<Elem *> >::iterator _map_iterator549 = _histogram537.find(_var536);
        if ((_map_iterator549 == _histogram537.end())) {
          _map_iterator549 = (_histogram537.emplace(_var536, 0).first);
        }
        int &_count540 = _map_iterator549->second;

        _count540 = (_count540 - 1);
      } else {
        _var535.push_back(_var536);
      }
    }
    {
      std::unordered_map< Elem *, int , std::hash<Elem *> >::const_iterator _map_iterator550 = (_histogram537.find(e));
      int _v551;
      if ((_map_iterator550 == _histogram537.end())) {
        _v551 = 0;
      } else {
        _v551 = (_map_iterator550->second);
      }
      if ((_v551 > 0)) {
        std::unordered_map< Elem *, int , std::hash<Elem *> >::iterator _map_iterator552 = _histogram537.find(e);
        if ((_map_iterator552 == _histogram537.end())) {
          _map_iterator552 = (_histogram537.emplace(e, 0).first);
        }
        int &_count540 = _map_iterator552->second;

        _count540 = (_count540 - 1);
      } else {
        _var535.push_back(e);
      }
    }
    std::vector< Elem * > _var495 = std::move(_var535);
    for (Elem *_var170 : _var494) {
      auto _it553(::std::find(_var116.begin(), _var116.end(), _var170));
      if (_it553 != _var116.end()) { _var116.erase(_it553); }
    }
    for (Elem *_var170 : _var495) {
      _var116.push_back(_var170);
    }
  }
};
