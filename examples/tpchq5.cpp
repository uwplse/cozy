#pragma once
#include <algorithm>
#include <functional>
#include <vector>
#include <unordered_set>
#include <string>
#include <unordered_map>

class TPCHQ5 {
public:
  struct _Type20303 {
    int id;
    std::string name;
    inline _Type20303() { }
    inline _Type20303(int _id, std::string _name) : id(::std::move(_id)), name(::std::move(_name)) { }
    inline bool operator==(const _Type20303& other) const {
      bool _v20314;
      if (((((*this).id) == (other.id)))) {
        _v20314 = ((((*this).name) == (other.name)));
      } else {
        _v20314 = false;
      }
      return _v20314;
    }
  };
  struct _Hash_Type20303 {
    typedef TPCHQ5::_Type20303 argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code20315 = 0;
      int _hash_code20316 = 0;
      _hash_code20316 = (std::hash<int >()((x.id)));
      _hash_code20315 = ((_hash_code20315 * 31) ^ (_hash_code20316));
      _hash_code20316 = (std::hash<std::string >()((x.name)));
      _hash_code20315 = ((_hash_code20315 * 31) ^ (_hash_code20316));
      return _hash_code20315;
    }
  };
  struct Region {
  public:
    _Type20303 val;
  private:
  };
    struct _Type20305 {
    int id;
    Region *region;
    inline _Type20305() { }
    inline _Type20305(int _id, Region *_region) : id(::std::move(_id)), region(::std::move(_region)) { }
    inline bool operator==(const _Type20305& other) const {
      bool _v20317;
      if (((((*this).id) == (other.id)))) {
        _v20317 = ((((*this).region) == (other.region)));
      } else {
        _v20317 = false;
      }
      return _v20317;
    }
  };
  struct _Hash_Type20305 {
    typedef TPCHQ5::_Type20305 argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code20318 = 0;
      int _hash_code20319 = 0;
      _hash_code20319 = (std::hash<int >()((x.id)));
      _hash_code20318 = ((_hash_code20318 * 31) ^ (_hash_code20319));
      _hash_code20319 = (std::hash<Region *>()((x.region)));
      _hash_code20318 = ((_hash_code20318 * 31) ^ (_hash_code20319));
      return _hash_code20318;
    }
  };
  struct Nation {
  public:
    _Type20305 val;
  private:
  };
    struct _Type20307 {
    int id;
    Nation *nation;
    inline _Type20307() { }
    inline _Type20307(int _id, Nation *_nation) : id(::std::move(_id)), nation(::std::move(_nation)) { }
    inline bool operator==(const _Type20307& other) const {
      bool _v20320;
      if (((((*this).id) == (other.id)))) {
        _v20320 = ((((*this).nation) == (other.nation)));
      } else {
        _v20320 = false;
      }
      return _v20320;
    }
  };
  struct _Hash_Type20307 {
    typedef TPCHQ5::_Type20307 argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code20321 = 0;
      int _hash_code20322 = 0;
      _hash_code20322 = (std::hash<int >()((x.id)));
      _hash_code20321 = ((_hash_code20321 * 31) ^ (_hash_code20322));
      _hash_code20322 = (std::hash<Nation *>()((x.nation)));
      _hash_code20321 = ((_hash_code20321 * 31) ^ (_hash_code20322));
      return _hash_code20321;
    }
  };
  struct Supplier {
  public:
    _Type20307 val;
  private:
  };
    struct Customer {
  public:
    _Type20307 val;
  private:
  };
    struct _Type20310 {
    int id;
    int orderdate;
    Customer *customer;
    inline _Type20310() { }
    inline _Type20310(int _id, int _orderdate, Customer *_customer) : id(::std::move(_id)), orderdate(::std::move(_orderdate)), customer(::std::move(_customer)) { }
    inline bool operator==(const _Type20310& other) const {
      bool _v20323;
      if (((((*this).id) == (other.id)))) {
        bool _v20324;
        if (((((*this).orderdate) == (other.orderdate)))) {
          _v20324 = ((((*this).customer) == (other.customer)));
        } else {
          _v20324 = false;
        }
        _v20323 = _v20324;
      } else {
        _v20323 = false;
      }
      return _v20323;
    }
  };
  struct _Hash_Type20310 {
    typedef TPCHQ5::_Type20310 argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code20325 = 0;
      int _hash_code20326 = 0;
      _hash_code20326 = (std::hash<int >()((x.id)));
      _hash_code20325 = ((_hash_code20325 * 31) ^ (_hash_code20326));
      _hash_code20326 = (std::hash<int >()((x.orderdate)));
      _hash_code20325 = ((_hash_code20325 * 31) ^ (_hash_code20326));
      _hash_code20326 = (std::hash<Customer *>()((x.customer)));
      _hash_code20325 = ((_hash_code20325 * 31) ^ (_hash_code20326));
      return _hash_code20325;
    }
  };
  struct Order {
  public:
    _Type20310 val;
  private:
  };
    struct _Type20312 {
    int id;
    float extendedprice;
    float discount;
    Supplier *supplier;
    Order *order;
    inline _Type20312() { }
    inline _Type20312(int _id, float _extendedprice, float _discount, Supplier *_supplier, Order *_order) : id(::std::move(_id)), extendedprice(::std::move(_extendedprice)), discount(::std::move(_discount)), supplier(::std::move(_supplier)), order(::std::move(_order)) { }
    inline bool operator==(const _Type20312& other) const {
      bool _v20327;
      bool _v20328;
      if (((((*this).id) == (other.id)))) {
        _v20328 = ((((*this).extendedprice) == (other.extendedprice)));
      } else {
        _v20328 = false;
      }
      if (_v20328) {
        bool _v20329;
        if (((((*this).discount) == (other.discount)))) {
          bool _v20330;
          if (((((*this).supplier) == (other.supplier)))) {
            _v20330 = ((((*this).order) == (other.order)));
          } else {
            _v20330 = false;
          }
          _v20329 = _v20330;
        } else {
          _v20329 = false;
        }
        _v20327 = _v20329;
      } else {
        _v20327 = false;
      }
      return _v20327;
    }
  };
  struct _Hash_Type20312 {
    typedef TPCHQ5::_Type20312 argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code20331 = 0;
      int _hash_code20332 = 0;
      _hash_code20332 = (std::hash<int >()((x.id)));
      _hash_code20331 = ((_hash_code20331 * 31) ^ (_hash_code20332));
      _hash_code20332 = (std::hash<float >()((x.extendedprice)));
      _hash_code20331 = ((_hash_code20331 * 31) ^ (_hash_code20332));
      _hash_code20332 = (std::hash<float >()((x.discount)));
      _hash_code20331 = ((_hash_code20331 * 31) ^ (_hash_code20332));
      _hash_code20332 = (std::hash<Supplier *>()((x.supplier)));
      _hash_code20331 = ((_hash_code20331 * 31) ^ (_hash_code20332));
      _hash_code20332 = (std::hash<Order *>()((x.order)));
      _hash_code20331 = ((_hash_code20331 * 31) ^ (_hash_code20332));
      return _hash_code20331;
    }
  };
  struct Lineitem {
  public:
    _Type20312 val;
  private:
  };
  protected:
  std::vector< Lineitem * > _var12490;
public:
  inline TPCHQ5() {
    _var12490 = (std::vector< Lineitem * > ());
  }
  explicit inline TPCHQ5(std::vector< Lineitem * > lineitems) {
    _var12490 = lineitems;
  }
  TPCHQ5(const TPCHQ5& other) = delete;
  template <class F>
  inline void selectLineitems(std::string p1, int p2, int p3, const F& _callback) {
    std::unordered_set< int , std::hash<int > > _distinct_elems20340 = (std::unordered_set< int , std::hash<int > > ());
    for (Lineitem *_i20341 : _var12490) {
      {
        _Type20312 _v20342;
        if (((_i20341 == nullptr))) {
          _v20342 = (_Type20312 (0, 0.0f, 0.0f, nullptr, nullptr));
        } else {
          _v20342 = (_i20341->val);
        }
        _Type20307 _v20343;
        if ((((_v20342.supplier) == nullptr))) {
          _v20343 = (_Type20307 (0, nullptr));
        } else {
          _v20343 = ((_v20342.supplier)->val);
        }
        _Type20305 _v20344;
        if ((((_v20343.nation) == nullptr))) {
          _v20344 = (_Type20305 (0, nullptr));
        } else {
          _v20344 = ((_v20343.nation)->val);
        }
        int _id20334 = (_v20344.id);
        if ((!((_distinct_elems20340.find(_id20334) != _distinct_elems20340.end())))) {
          float _sum20335 = 0.0f;
          for (Lineitem *_i20339 : _var12490) {
            bool _v20345;
            bool _v20346;
            bool _v20347;
            bool _v20348;
            _Type20312 _v20349;
            if (((_i20339 == nullptr))) {
              _v20349 = (_Type20312 (0, 0.0f, 0.0f, nullptr, nullptr));
            } else {
              _v20349 = (_i20339->val);
            }
            _Type20310 _v20350;
            if ((((_v20349.order) == nullptr))) {
              _v20350 = (_Type20310 (0, 0, nullptr));
            } else {
              _v20350 = ((_v20349.order)->val);
            }
            if (((_v20350.orderdate) <= p3)) {
              _Type20312 _v20351;
              if (((_i20339 == nullptr))) {
                _v20351 = (_Type20312 (0, 0.0f, 0.0f, nullptr, nullptr));
              } else {
                _v20351 = (_i20339->val);
              }
              _Type20310 _v20352;
              if ((((_v20351.order) == nullptr))) {
                _v20352 = (_Type20310 (0, 0, nullptr));
              } else {
                _v20352 = ((_v20351.order)->val);
              }
              _v20348 = ((_v20352.orderdate) >= p2);
            } else {
              _v20348 = false;
            }
            if (_v20348) {
              _Type20312 _v20353;
              if (((_i20339 == nullptr))) {
                _v20353 = (_Type20312 (0, 0.0f, 0.0f, nullptr, nullptr));
              } else {
                _v20353 = (_i20339->val);
              }
              _Type20310 _v20354;
              if ((((_v20353.order) == nullptr))) {
                _v20354 = (_Type20310 (0, 0, nullptr));
              } else {
                _v20354 = ((_v20353.order)->val);
              }
              _Type20307 _v20355;
              if ((((_v20354.customer) == nullptr))) {
                _v20355 = (_Type20307 (0, nullptr));
              } else {
                _v20355 = ((_v20354.customer)->val);
              }
              _Type20305 _v20356;
              if ((((_v20355.nation) == nullptr))) {
                _v20356 = (_Type20305 (0, nullptr));
              } else {
                _v20356 = ((_v20355.nation)->val);
              }
              _Type20312 _v20357;
              if (((_i20339 == nullptr))) {
                _v20357 = (_Type20312 (0, 0.0f, 0.0f, nullptr, nullptr));
              } else {
                _v20357 = (_i20339->val);
              }
              _Type20307 _v20358;
              if ((((_v20357.supplier) == nullptr))) {
                _v20358 = (_Type20307 (0, nullptr));
              } else {
                _v20358 = ((_v20357.supplier)->val);
              }
              _Type20305 _v20359;
              if ((((_v20358.nation) == nullptr))) {
                _v20359 = (_Type20305 (0, nullptr));
              } else {
                _v20359 = ((_v20358.nation)->val);
              }
              _v20347 = (((_v20356.id) == (_v20359.id)));
            } else {
              _v20347 = false;
            }
            if (_v20347) {
              _Type20312 _v20360;
              if (((_i20339 == nullptr))) {
                _v20360 = (_Type20312 (0, 0.0f, 0.0f, nullptr, nullptr));
              } else {
                _v20360 = (_i20339->val);
              }
              _Type20307 _v20361;
              if ((((_v20360.supplier) == nullptr))) {
                _v20361 = (_Type20307 (0, nullptr));
              } else {
                _v20361 = ((_v20360.supplier)->val);
              }
              _Type20305 _v20362;
              if ((((_v20361.nation) == nullptr))) {
                _v20362 = (_Type20305 (0, nullptr));
              } else {
                _v20362 = ((_v20361.nation)->val);
              }
              _Type20303 _v20363;
              if ((((_v20362.region) == nullptr))) {
                _v20363 = (_Type20303 (0, ""));
              } else {
                _v20363 = ((_v20362.region)->val);
              }
              _v20346 = (((_v20363.name) == p1));
            } else {
              _v20346 = false;
            }
            if (_v20346) {
              _Type20312 _v20364;
              if (((_i20339 == nullptr))) {
                _v20364 = (_Type20312 (0, 0.0f, 0.0f, nullptr, nullptr));
              } else {
                _v20364 = (_i20339->val);
              }
              _Type20307 _v20365;
              if ((((_v20364.supplier) == nullptr))) {
                _v20365 = (_Type20307 (0, nullptr));
              } else {
                _v20365 = ((_v20364.supplier)->val);
              }
              _Type20305 _v20366;
              if ((((_v20365.nation) == nullptr))) {
                _v20366 = (_Type20305 (0, nullptr));
              } else {
                _v20366 = ((_v20365.nation)->val);
              }
              _v20345 = (((_v20366.id) == _id20334));
            } else {
              _v20345 = false;
            }
            if (_v20345) {
              {
                {
                  {
                    _Type20312 _v20367;
                    if (((_i20339 == nullptr))) {
                      _v20367 = (_Type20312 (0, 0.0f, 0.0f, nullptr, nullptr));
                    } else {
                      _v20367 = (_i20339->val);
                    }
                    _Type20312 _v20368;
                    if (((_i20339 == nullptr))) {
                      _v20368 = (_Type20312 (0, 0.0f, 0.0f, nullptr, nullptr));
                    } else {
                      _v20368 = (_i20339->val);
                    }
                    _sum20335 = (_sum20335 + (((_v20367.extendedprice)) * ((1.0f - (_v20368.discount)))));
                  }
                }
              }
            }
          }
          {
            _callback(_sum20335);
          }
          _distinct_elems20340.insert(_id20334);
        }
      }
    }
  }
  inline void insertLineitem (Lineitem *i) {
    std::vector< Lineitem * > _var20369 = (std::vector< Lineitem * > ());
    std::unordered_map< Lineitem *, int , std::hash<Lineitem *> > _histogram20371 = (std::unordered_map< Lineitem *, int , std::hash<Lineitem *> > ());
    for (Lineitem *_x20372 : _var12490) {
      std::unordered_map< Lineitem *, int , std::hash<Lineitem *> >::iterator _map_iterator20381 = _histogram20371.find(_x20372);
      if ((_map_iterator20381 == _histogram20371.end())) {
        _map_iterator20381 = (_histogram20371.emplace(_x20372, 0).first);
      }
      int &_count20373 = _map_iterator20381->second;

      _count20373 = (_count20373 + 1);
    }
    {
      std::unordered_map< Lineitem *, int , std::hash<Lineitem *> >::iterator _map_iterator20382 = _histogram20371.find(i);
      if ((_map_iterator20382 == _histogram20371.end())) {
        _map_iterator20382 = (_histogram20371.emplace(i, 0).first);
      }
      int &_count20373 = _map_iterator20382->second;

      _count20373 = (_count20373 + 1);
    }
    for (Lineitem *_var20370 : _var12490) {
      std::unordered_map< Lineitem *, int , std::hash<Lineitem *> >::const_iterator _map_iterator20383 = (_histogram20371.find(_var20370));
      int _v20384;
      if ((_map_iterator20383 == _histogram20371.end())) {
        _v20384 = 0;
      } else {
        _v20384 = (_map_iterator20383->second);
      }
      if ((_v20384 > 0)) {
        std::unordered_map< Lineitem *, int , std::hash<Lineitem *> >::iterator _map_iterator20385 = _histogram20371.find(_var20370);
        if ((_map_iterator20385 == _histogram20371.end())) {
          _map_iterator20385 = (_histogram20371.emplace(_var20370, 0).first);
        }
        int &_count20374 = _map_iterator20385->second;

        _count20374 = (_count20374 - 1);
      } else {
        _var20369.push_back(_var20370);
      }
    }
    std::vector< Lineitem * > _var20235 = std::move(_var20369);
    std::vector< Lineitem * > _var20375 = (std::vector< Lineitem * > ());
    std::unordered_map< Lineitem *, int , std::hash<Lineitem *> > _histogram20377 = (std::unordered_map< Lineitem *, int , std::hash<Lineitem *> > ());
    for (Lineitem *_x20378 : _var12490) {
      std::unordered_map< Lineitem *, int , std::hash<Lineitem *> >::iterator _map_iterator20386 = _histogram20377.find(_x20378);
      if ((_map_iterator20386 == _histogram20377.end())) {
        _map_iterator20386 = (_histogram20377.emplace(_x20378, 0).first);
      }
      int &_count20379 = _map_iterator20386->second;

      _count20379 = (_count20379 + 1);
    }
    for (Lineitem *_var20376 : _var12490) {
      std::unordered_map< Lineitem *, int , std::hash<Lineitem *> >::const_iterator _map_iterator20387 = (_histogram20377.find(_var20376));
      int _v20388;
      if ((_map_iterator20387 == _histogram20377.end())) {
        _v20388 = 0;
      } else {
        _v20388 = (_map_iterator20387->second);
      }
      if ((_v20388 > 0)) {
        std::unordered_map< Lineitem *, int , std::hash<Lineitem *> >::iterator _map_iterator20389 = _histogram20377.find(_var20376);
        if ((_map_iterator20389 == _histogram20377.end())) {
          _map_iterator20389 = (_histogram20377.emplace(_var20376, 0).first);
        }
        int &_count20380 = _map_iterator20389->second;

        _count20380 = (_count20380 - 1);
      } else {
        _var20375.push_back(_var20376);
      }
    }
    {
      std::unordered_map< Lineitem *, int , std::hash<Lineitem *> >::const_iterator _map_iterator20390 = (_histogram20377.find(i));
      int _v20391;
      if ((_map_iterator20390 == _histogram20377.end())) {
        _v20391 = 0;
      } else {
        _v20391 = (_map_iterator20390->second);
      }
      if ((_v20391 > 0)) {
        std::unordered_map< Lineitem *, int , std::hash<Lineitem *> >::iterator _map_iterator20392 = _histogram20377.find(i);
        if ((_map_iterator20392 == _histogram20377.end())) {
          _map_iterator20392 = (_histogram20377.emplace(i, 0).first);
        }
        int &_count20380 = _map_iterator20392->second;

        _count20380 = (_count20380 - 1);
      } else {
        _var20375.push_back(i);
      }
    }
    std::vector< Lineitem * > _var20236 = std::move(_var20375);
    for (Lineitem *_var13058 : _var20235) {
      auto _it20393(::std::find(_var12490.begin(), _var12490.end(), _var13058));
      if (_it20393 != _var12490.end()) { _var12490.erase(_it20393); }
    }
    for (Lineitem *_var13058 : _var20236) {
      _var12490.push_back(_var13058);
    }
  }
};
