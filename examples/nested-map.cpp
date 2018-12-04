#pragma once
#include <algorithm>
#include <functional>
#include <vector>
#include <unordered_set>
#include <string>
#include <unordered_map>

class In {
public:
  struct _Type61 {
    int _0;
    int _1;
    inline _Type61() { }
    inline _Type61(int __0, int __1) : _0(::std::move(__0)), _1(::std::move(__1)) { }
    inline bool operator==(const _Type61& other) const {
      bool _v63;
      if (((((*this)._0) == (other._0)))) {
        _v63 = ((((*this)._1) == (other._1)));
      } else {
        _v63 = false;
      }
      return _v63;
    }
  };
  struct _Hash_Type61 {
    typedef In::_Type61 argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code64 = 0;
      int _hash_code65 = 0;
      _hash_code65 = (std::hash<int >()((x._0)));
      _hash_code64 = ((_hash_code64 * 31) ^ (_hash_code65));
      _hash_code65 = (std::hash<int >()((x._1)));
      _hash_code64 = ((_hash_code64 * 31) ^ (_hash_code65));
      return _hash_code64;
    }
  };
  struct Elem {
  public:
    _Type61 val;
  private:
  };
  protected:
  std::vector< Elem * > _var50;
public:
  inline In() {
    _var50 = (std::vector< Elem * > ());
  }
  explicit inline In(std::vector< Elem * > xs) {
    _var50 = xs;
  }
  In(const In& other) = delete;
  template <class F>
  inline void a(int st, int ed, const F& _callback) {
    for (Elem *_x68 : _var50) {
      bool _v69;
      _Type61 _v70;
      if (((_x68 == nullptr))) {
        _v70 = (_Type61(0, 0));
      } else {
        _v70 = (_x68->val);
      }
      if ((((_v70._1) == ed))) {
        _Type61 _v71;
        if (((_x68 == nullptr))) {
          _v71 = (_Type61(0, 0));
        } else {
          _v71 = (_x68->val);
        }
        _v69 = (((_v71._0) == st));
      } else {
        _v69 = false;
      }
      if (_v69) {
        {
          {
            _callback(_x68);
          }
        }
      }
    }
  }
};
