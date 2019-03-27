#pragma once
#include <algorithm>
#include <set>
#include <functional>
#include <vector>
#include <unordered_set>
#include <string>
#include <unordered_map>

class TPCH_Store {
public:
  struct LINEITEM {
    int orderkey;
    int partkey;
    int suppkey;
    int linenumber;
    float quantity;
    float extendedprice;
    float discount;
    float tax;
    char returnflag;
    char linestatus;
    int shipdate;
    int commitdate;
    int receiptdate;
    std::string shipinstruct;
    std::string shipmode;
    std::string comment;
    inline LINEITEM() { }
    inline LINEITEM(int _orderkey, int _partkey, int _suppkey, int _linenumber, float _quantity, float _extendedprice, float _discount, float _tax, char _returnflag, char _linestatus, int _shipdate, int _commitdate, int _receiptdate, std::string _shipinstruct, std::string _shipmode, std::string _comment) : orderkey(::std::move(_orderkey)), partkey(::std::move(_partkey)), suppkey(::std::move(_suppkey)), linenumber(::std::move(_linenumber)), quantity(::std::move(_quantity)), extendedprice(::std::move(_extendedprice)), discount(::std::move(_discount)), tax(::std::move(_tax)), returnflag(::std::move(_returnflag)), linestatus(::std::move(_linestatus)), shipdate(::std::move(_shipdate)), commitdate(::std::move(_commitdate)), receiptdate(::std::move(_receiptdate)), shipinstruct(::std::move(_shipinstruct)), shipmode(::std::move(_shipmode)), comment(::std::move(_comment)) { }
    inline bool operator==(const LINEITEM& other) const {
      bool _v338677;
      bool _v338678;
      bool _v338679;
      bool _v338680;
      if (((((*this).orderkey) == (other.orderkey)))) {
        _v338680 = ((((*this).partkey) == (other.partkey)));
      } else {
        _v338680 = false;
      }
      if (_v338680) {
        bool _v338681;
        if (((((*this).suppkey) == (other.suppkey)))) {
          _v338681 = ((((*this).linenumber) == (other.linenumber)));
        } else {
          _v338681 = false;
        }
        _v338679 = _v338681;
      } else {
        _v338679 = false;
      }
      if (_v338679) {
        bool _v338682;
        bool _v338683;
        if (((((*this).quantity) == (other.quantity)))) {
          _v338683 = ((((*this).extendedprice) == (other.extendedprice)));
        } else {
          _v338683 = false;
        }
        if (_v338683) {
          bool _v338684;
          if (((((*this).discount) == (other.discount)))) {
            _v338684 = ((((*this).tax) == (other.tax)));
          } else {
            _v338684 = false;
          }
          _v338682 = _v338684;
        } else {
          _v338682 = false;
        }
        _v338678 = _v338682;
      } else {
        _v338678 = false;
      }
      if (_v338678) {
        bool _v338685;
        bool _v338686;
        bool _v338687;
        if (((((*this).returnflag) == (other.returnflag)))) {
          _v338687 = ((((*this).linestatus) == (other.linestatus)));
        } else {
          _v338687 = false;
        }
        if (_v338687) {
          bool _v338688;
          if (((((*this).shipdate) == (other.shipdate)))) {
            _v338688 = ((((*this).commitdate) == (other.commitdate)));
          } else {
            _v338688 = false;
          }
          _v338686 = _v338688;
        } else {
          _v338686 = false;
        }
        if (_v338686) {
          bool _v338689;
          bool _v338690;
          if (((((*this).receiptdate) == (other.receiptdate)))) {
            _v338690 = ((((*this).shipinstruct) == (other.shipinstruct)));
          } else {
            _v338690 = false;
          }
          if (_v338690) {
            bool _v338691;
            if (((((*this).shipmode) == (other.shipmode)))) {
              _v338691 = ((((*this).comment) == (other.comment)));
            } else {
              _v338691 = false;
            }
            _v338689 = _v338691;
          } else {
            _v338689 = false;
          }
          _v338685 = _v338689;
        } else {
          _v338685 = false;
        }
        _v338677 = _v338685;
      } else {
        _v338677 = false;
      }
      return _v338677;
    }
  };
  struct _HashLINEITEM {
    typedef TPCH_Store::LINEITEM argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code338692 = 0;
      int _hash_code338693 = 0;
      _hash_code338693 = (std::hash<int >()((x.orderkey)));
      _hash_code338692 = ((_hash_code338692 * 31) ^ (_hash_code338693));
      _hash_code338693 = (std::hash<int >()((x.partkey)));
      _hash_code338692 = ((_hash_code338692 * 31) ^ (_hash_code338693));
      _hash_code338693 = (std::hash<int >()((x.suppkey)));
      _hash_code338692 = ((_hash_code338692 * 31) ^ (_hash_code338693));
      _hash_code338693 = (std::hash<int >()((x.linenumber)));
      _hash_code338692 = ((_hash_code338692 * 31) ^ (_hash_code338693));
      _hash_code338693 = (std::hash<float >()((x.quantity)));
      _hash_code338692 = ((_hash_code338692 * 31) ^ (_hash_code338693));
      _hash_code338693 = (std::hash<float >()((x.extendedprice)));
      _hash_code338692 = ((_hash_code338692 * 31) ^ (_hash_code338693));
      _hash_code338693 = (std::hash<float >()((x.discount)));
      _hash_code338692 = ((_hash_code338692 * 31) ^ (_hash_code338693));
      _hash_code338693 = (std::hash<float >()((x.tax)));
      _hash_code338692 = ((_hash_code338692 * 31) ^ (_hash_code338693));
      _hash_code338693 = (std::hash<char >()((x.returnflag)));
      _hash_code338692 = ((_hash_code338692 * 31) ^ (_hash_code338693));
      _hash_code338693 = (std::hash<char >()((x.linestatus)));
      _hash_code338692 = ((_hash_code338692 * 31) ^ (_hash_code338693));
      _hash_code338693 = (std::hash<int >()((x.shipdate)));
      _hash_code338692 = ((_hash_code338692 * 31) ^ (_hash_code338693));
      _hash_code338693 = (std::hash<int >()((x.commitdate)));
      _hash_code338692 = ((_hash_code338692 * 31) ^ (_hash_code338693));
      _hash_code338693 = (std::hash<int >()((x.receiptdate)));
      _hash_code338692 = ((_hash_code338692 * 31) ^ (_hash_code338693));
      _hash_code338693 = (std::hash<std::string >()((x.shipinstruct)));
      _hash_code338692 = ((_hash_code338692 * 31) ^ (_hash_code338693));
      _hash_code338693 = (std::hash<std::string >()((x.shipmode)));
      _hash_code338692 = ((_hash_code338692 * 31) ^ (_hash_code338693));
      _hash_code338693 = (std::hash<std::string >()((x.comment)));
      _hash_code338692 = ((_hash_code338692 * 31) ^ (_hash_code338693));
      return _hash_code338692;
    }
  };
  struct ORDERS {
    int orderkey;
    int custkey;
    char orderstatus;
    float totalprice;
    int orderdate;
    std::string orderpriority;
    std::string clerk;
    int shippriority;
    std::string comment;
    inline ORDERS() { }
    inline ORDERS(int _orderkey, int _custkey, char _orderstatus, float _totalprice, int _orderdate, std::string _orderpriority, std::string _clerk, int _shippriority, std::string _comment) : orderkey(::std::move(_orderkey)), custkey(::std::move(_custkey)), orderstatus(::std::move(_orderstatus)), totalprice(::std::move(_totalprice)), orderdate(::std::move(_orderdate)), orderpriority(::std::move(_orderpriority)), clerk(::std::move(_clerk)), shippriority(::std::move(_shippriority)), comment(::std::move(_comment)) { }
    inline bool operator==(const ORDERS& other) const {
      bool _v338694;
      bool _v338695;
      bool _v338696;
      if (((((*this).orderkey) == (other.orderkey)))) {
        _v338696 = ((((*this).custkey) == (other.custkey)));
      } else {
        _v338696 = false;
      }
      if (_v338696) {
        bool _v338697;
        if (((((*this).orderstatus) == (other.orderstatus)))) {
          _v338697 = ((((*this).totalprice) == (other.totalprice)));
        } else {
          _v338697 = false;
        }
        _v338695 = _v338697;
      } else {
        _v338695 = false;
      }
      if (_v338695) {
        bool _v338698;
        bool _v338699;
        if (((((*this).orderdate) == (other.orderdate)))) {
          _v338699 = ((((*this).orderpriority) == (other.orderpriority)));
        } else {
          _v338699 = false;
        }
        if (_v338699) {
          bool _v338700;
          if (((((*this).clerk) == (other.clerk)))) {
            bool _v338701;
            if (((((*this).shippriority) == (other.shippriority)))) {
              _v338701 = ((((*this).comment) == (other.comment)));
            } else {
              _v338701 = false;
            }
            _v338700 = _v338701;
          } else {
            _v338700 = false;
          }
          _v338698 = _v338700;
        } else {
          _v338698 = false;
        }
        _v338694 = _v338698;
      } else {
        _v338694 = false;
      }
      return _v338694;
    }
  };
  struct _HashORDERS {
    typedef TPCH_Store::ORDERS argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code338702 = 0;
      int _hash_code338703 = 0;
      _hash_code338703 = (std::hash<int >()((x.orderkey)));
      _hash_code338702 = ((_hash_code338702 * 31) ^ (_hash_code338703));
      _hash_code338703 = (std::hash<int >()((x.custkey)));
      _hash_code338702 = ((_hash_code338702 * 31) ^ (_hash_code338703));
      _hash_code338703 = (std::hash<char >()((x.orderstatus)));
      _hash_code338702 = ((_hash_code338702 * 31) ^ (_hash_code338703));
      _hash_code338703 = (std::hash<float >()((x.totalprice)));
      _hash_code338702 = ((_hash_code338702 * 31) ^ (_hash_code338703));
      _hash_code338703 = (std::hash<int >()((x.orderdate)));
      _hash_code338702 = ((_hash_code338702 * 31) ^ (_hash_code338703));
      _hash_code338703 = (std::hash<std::string >()((x.orderpriority)));
      _hash_code338702 = ((_hash_code338702 * 31) ^ (_hash_code338703));
      _hash_code338703 = (std::hash<std::string >()((x.clerk)));
      _hash_code338702 = ((_hash_code338702 * 31) ^ (_hash_code338703));
      _hash_code338703 = (std::hash<int >()((x.shippriority)));
      _hash_code338702 = ((_hash_code338702 * 31) ^ (_hash_code338703));
      _hash_code338703 = (std::hash<std::string >()((x.comment)));
      _hash_code338702 = ((_hash_code338702 * 31) ^ (_hash_code338703));
      return _hash_code338702;
    }
  };
  struct PART {
    int partkey;
    std::string name;
    std::string mfgr;
    std::string brand;
    std::string part_type;
    int size;
    std::string container;
    float retailprice;
    std::string comment;
    inline PART() { }
    inline PART(int _partkey, std::string _name, std::string _mfgr, std::string _brand, std::string _part_type, int _size, std::string _container, float _retailprice, std::string _comment) : partkey(::std::move(_partkey)), name(::std::move(_name)), mfgr(::std::move(_mfgr)), brand(::std::move(_brand)), part_type(::std::move(_part_type)), size(::std::move(_size)), container(::std::move(_container)), retailprice(::std::move(_retailprice)), comment(::std::move(_comment)) { }
    inline bool operator==(const PART& other) const {
      bool _v338704;
      bool _v338705;
      bool _v338706;
      if (((((*this).partkey) == (other.partkey)))) {
        _v338706 = ((((*this).name) == (other.name)));
      } else {
        _v338706 = false;
      }
      if (_v338706) {
        bool _v338707;
        if (((((*this).mfgr) == (other.mfgr)))) {
          _v338707 = ((((*this).brand) == (other.brand)));
        } else {
          _v338707 = false;
        }
        _v338705 = _v338707;
      } else {
        _v338705 = false;
      }
      if (_v338705) {
        bool _v338708;
        bool _v338709;
        if (((((*this).part_type) == (other.part_type)))) {
          _v338709 = ((((*this).size) == (other.size)));
        } else {
          _v338709 = false;
        }
        if (_v338709) {
          bool _v338710;
          if (((((*this).container) == (other.container)))) {
            bool _v338711;
            if (((((*this).retailprice) == (other.retailprice)))) {
              _v338711 = ((((*this).comment) == (other.comment)));
            } else {
              _v338711 = false;
            }
            _v338710 = _v338711;
          } else {
            _v338710 = false;
          }
          _v338708 = _v338710;
        } else {
          _v338708 = false;
        }
        _v338704 = _v338708;
      } else {
        _v338704 = false;
      }
      return _v338704;
    }
  };
  struct _HashPART {
    typedef TPCH_Store::PART argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code338712 = 0;
      int _hash_code338713 = 0;
      _hash_code338713 = (std::hash<int >()((x.partkey)));
      _hash_code338712 = ((_hash_code338712 * 31) ^ (_hash_code338713));
      _hash_code338713 = (std::hash<std::string >()((x.name)));
      _hash_code338712 = ((_hash_code338712 * 31) ^ (_hash_code338713));
      _hash_code338713 = (std::hash<std::string >()((x.mfgr)));
      _hash_code338712 = ((_hash_code338712 * 31) ^ (_hash_code338713));
      _hash_code338713 = (std::hash<std::string >()((x.brand)));
      _hash_code338712 = ((_hash_code338712 * 31) ^ (_hash_code338713));
      _hash_code338713 = (std::hash<std::string >()((x.part_type)));
      _hash_code338712 = ((_hash_code338712 * 31) ^ (_hash_code338713));
      _hash_code338713 = (std::hash<int >()((x.size)));
      _hash_code338712 = ((_hash_code338712 * 31) ^ (_hash_code338713));
      _hash_code338713 = (std::hash<std::string >()((x.container)));
      _hash_code338712 = ((_hash_code338712 * 31) ^ (_hash_code338713));
      _hash_code338713 = (std::hash<float >()((x.retailprice)));
      _hash_code338712 = ((_hash_code338712 * 31) ^ (_hash_code338713));
      _hash_code338713 = (std::hash<std::string >()((x.comment)));
      _hash_code338712 = ((_hash_code338712 * 31) ^ (_hash_code338713));
      return _hash_code338712;
    }
  };
  struct CUSTOMER {
    int custkey;
    std::string name;
    std::string address;
    int nationkey;
    std::string phone;
    float acctbal;
    std::string mktsegment;
    std::string comment;
    inline CUSTOMER() { }
    inline CUSTOMER(int _custkey, std::string _name, std::string _address, int _nationkey, std::string _phone, float _acctbal, std::string _mktsegment, std::string _comment) : custkey(::std::move(_custkey)), name(::std::move(_name)), address(::std::move(_address)), nationkey(::std::move(_nationkey)), phone(::std::move(_phone)), acctbal(::std::move(_acctbal)), mktsegment(::std::move(_mktsegment)), comment(::std::move(_comment)) { }
    inline bool operator==(const CUSTOMER& other) const {
      bool _v338714;
      bool _v338715;
      bool _v338716;
      if (((((*this).custkey) == (other.custkey)))) {
        _v338716 = ((((*this).name) == (other.name)));
      } else {
        _v338716 = false;
      }
      if (_v338716) {
        bool _v338717;
        if (((((*this).address) == (other.address)))) {
          _v338717 = ((((*this).nationkey) == (other.nationkey)));
        } else {
          _v338717 = false;
        }
        _v338715 = _v338717;
      } else {
        _v338715 = false;
      }
      if (_v338715) {
        bool _v338718;
        bool _v338719;
        if (((((*this).phone) == (other.phone)))) {
          _v338719 = ((((*this).acctbal) == (other.acctbal)));
        } else {
          _v338719 = false;
        }
        if (_v338719) {
          bool _v338720;
          if (((((*this).mktsegment) == (other.mktsegment)))) {
            _v338720 = ((((*this).comment) == (other.comment)));
          } else {
            _v338720 = false;
          }
          _v338718 = _v338720;
        } else {
          _v338718 = false;
        }
        _v338714 = _v338718;
      } else {
        _v338714 = false;
      }
      return _v338714;
    }
  };
  struct _HashCUSTOMER {
    typedef TPCH_Store::CUSTOMER argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code338721 = 0;
      int _hash_code338722 = 0;
      _hash_code338722 = (std::hash<int >()((x.custkey)));
      _hash_code338721 = ((_hash_code338721 * 31) ^ (_hash_code338722));
      _hash_code338722 = (std::hash<std::string >()((x.name)));
      _hash_code338721 = ((_hash_code338721 * 31) ^ (_hash_code338722));
      _hash_code338722 = (std::hash<std::string >()((x.address)));
      _hash_code338721 = ((_hash_code338721 * 31) ^ (_hash_code338722));
      _hash_code338722 = (std::hash<int >()((x.nationkey)));
      _hash_code338721 = ((_hash_code338721 * 31) ^ (_hash_code338722));
      _hash_code338722 = (std::hash<std::string >()((x.phone)));
      _hash_code338721 = ((_hash_code338721 * 31) ^ (_hash_code338722));
      _hash_code338722 = (std::hash<float >()((x.acctbal)));
      _hash_code338721 = ((_hash_code338721 * 31) ^ (_hash_code338722));
      _hash_code338722 = (std::hash<std::string >()((x.mktsegment)));
      _hash_code338721 = ((_hash_code338721 * 31) ^ (_hash_code338722));
      _hash_code338722 = (std::hash<std::string >()((x.comment)));
      _hash_code338721 = ((_hash_code338721 * 31) ^ (_hash_code338722));
      return _hash_code338721;
    }
  };
  struct SUPPLIER {
    int suppkey;
    std::string name;
    std::string address;
    int nationkey;
    std::string phone;
    float acctbal;
    std::string comment;
    inline SUPPLIER() { }
    inline SUPPLIER(int _suppkey, std::string _name, std::string _address, int _nationkey, std::string _phone, float _acctbal, std::string _comment) : suppkey(::std::move(_suppkey)), name(::std::move(_name)), address(::std::move(_address)), nationkey(::std::move(_nationkey)), phone(::std::move(_phone)), acctbal(::std::move(_acctbal)), comment(::std::move(_comment)) { }
    inline bool operator==(const SUPPLIER& other) const {
      bool _v338723;
      bool _v338724;
      if (((((*this).suppkey) == (other.suppkey)))) {
        bool _v338725;
        if (((((*this).name) == (other.name)))) {
          _v338725 = ((((*this).address) == (other.address)));
        } else {
          _v338725 = false;
        }
        _v338724 = _v338725;
      } else {
        _v338724 = false;
      }
      if (_v338724) {
        bool _v338726;
        bool _v338727;
        if (((((*this).nationkey) == (other.nationkey)))) {
          _v338727 = ((((*this).phone) == (other.phone)));
        } else {
          _v338727 = false;
        }
        if (_v338727) {
          bool _v338728;
          if (((((*this).acctbal) == (other.acctbal)))) {
            _v338728 = ((((*this).comment) == (other.comment)));
          } else {
            _v338728 = false;
          }
          _v338726 = _v338728;
        } else {
          _v338726 = false;
        }
        _v338723 = _v338726;
      } else {
        _v338723 = false;
      }
      return _v338723;
    }
  };
  struct _HashSUPPLIER {
    typedef TPCH_Store::SUPPLIER argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code338729 = 0;
      int _hash_code338730 = 0;
      _hash_code338730 = (std::hash<int >()((x.suppkey)));
      _hash_code338729 = ((_hash_code338729 * 31) ^ (_hash_code338730));
      _hash_code338730 = (std::hash<std::string >()((x.name)));
      _hash_code338729 = ((_hash_code338729 * 31) ^ (_hash_code338730));
      _hash_code338730 = (std::hash<std::string >()((x.address)));
      _hash_code338729 = ((_hash_code338729 * 31) ^ (_hash_code338730));
      _hash_code338730 = (std::hash<int >()((x.nationkey)));
      _hash_code338729 = ((_hash_code338729 * 31) ^ (_hash_code338730));
      _hash_code338730 = (std::hash<std::string >()((x.phone)));
      _hash_code338729 = ((_hash_code338729 * 31) ^ (_hash_code338730));
      _hash_code338730 = (std::hash<float >()((x.acctbal)));
      _hash_code338729 = ((_hash_code338729 * 31) ^ (_hash_code338730));
      _hash_code338730 = (std::hash<std::string >()((x.comment)));
      _hash_code338729 = ((_hash_code338729 * 31) ^ (_hash_code338730));
      return _hash_code338729;
    }
  };
  struct PARTSUPP {
    int partkey;
    int suppkey;
    int availqty;
    float supplycost;
    std::string comment;
    inline PARTSUPP() { }
    inline PARTSUPP(int _partkey, int _suppkey, int _availqty, float _supplycost, std::string _comment) : partkey(::std::move(_partkey)), suppkey(::std::move(_suppkey)), availqty(::std::move(_availqty)), supplycost(::std::move(_supplycost)), comment(::std::move(_comment)) { }
    inline bool operator==(const PARTSUPP& other) const {
      bool _v338731;
      bool _v338732;
      if (((((*this).partkey) == (other.partkey)))) {
        _v338732 = ((((*this).suppkey) == (other.suppkey)));
      } else {
        _v338732 = false;
      }
      if (_v338732) {
        bool _v338733;
        if (((((*this).availqty) == (other.availqty)))) {
          bool _v338734;
          if (((((*this).supplycost) == (other.supplycost)))) {
            _v338734 = ((((*this).comment) == (other.comment)));
          } else {
            _v338734 = false;
          }
          _v338733 = _v338734;
        } else {
          _v338733 = false;
        }
        _v338731 = _v338733;
      } else {
        _v338731 = false;
      }
      return _v338731;
    }
  };
  struct _HashPARTSUPP {
    typedef TPCH_Store::PARTSUPP argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code338735 = 0;
      int _hash_code338736 = 0;
      _hash_code338736 = (std::hash<int >()((x.partkey)));
      _hash_code338735 = ((_hash_code338735 * 31) ^ (_hash_code338736));
      _hash_code338736 = (std::hash<int >()((x.suppkey)));
      _hash_code338735 = ((_hash_code338735 * 31) ^ (_hash_code338736));
      _hash_code338736 = (std::hash<int >()((x.availqty)));
      _hash_code338735 = ((_hash_code338735 * 31) ^ (_hash_code338736));
      _hash_code338736 = (std::hash<float >()((x.supplycost)));
      _hash_code338735 = ((_hash_code338735 * 31) ^ (_hash_code338736));
      _hash_code338736 = (std::hash<std::string >()((x.comment)));
      _hash_code338735 = ((_hash_code338735 * 31) ^ (_hash_code338736));
      return _hash_code338735;
    }
  };
  struct NATION {
    int nationkey;
    std::string name;
    int regionkey;
    std::string comment;
    inline NATION() { }
    inline NATION(int _nationkey, std::string _name, int _regionkey, std::string _comment) : nationkey(::std::move(_nationkey)), name(::std::move(_name)), regionkey(::std::move(_regionkey)), comment(::std::move(_comment)) { }
    inline bool operator==(const NATION& other) const {
      bool _v338737;
      bool _v338738;
      if (((((*this).nationkey) == (other.nationkey)))) {
        _v338738 = ((((*this).name) == (other.name)));
      } else {
        _v338738 = false;
      }
      if (_v338738) {
        bool _v338739;
        if (((((*this).regionkey) == (other.regionkey)))) {
          _v338739 = ((((*this).comment) == (other.comment)));
        } else {
          _v338739 = false;
        }
        _v338737 = _v338739;
      } else {
        _v338737 = false;
      }
      return _v338737;
    }
  };
  struct _HashNATION {
    typedef TPCH_Store::NATION argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code338740 = 0;
      int _hash_code338741 = 0;
      _hash_code338741 = (std::hash<int >()((x.nationkey)));
      _hash_code338740 = ((_hash_code338740 * 31) ^ (_hash_code338741));
      _hash_code338741 = (std::hash<std::string >()((x.name)));
      _hash_code338740 = ((_hash_code338740 * 31) ^ (_hash_code338741));
      _hash_code338741 = (std::hash<int >()((x.regionkey)));
      _hash_code338740 = ((_hash_code338740 * 31) ^ (_hash_code338741));
      _hash_code338741 = (std::hash<std::string >()((x.comment)));
      _hash_code338740 = ((_hash_code338740 * 31) ^ (_hash_code338741));
      return _hash_code338740;
    }
  };
  struct REGION {
    int regionkey;
    std::string name;
    std::string comment;
    inline REGION() { }
    inline REGION(int _regionkey, std::string _name, std::string _comment) : regionkey(::std::move(_regionkey)), name(::std::move(_name)), comment(::std::move(_comment)) { }
    inline bool operator==(const REGION& other) const {
      bool _v338742;
      if (((((*this).regionkey) == (other.regionkey)))) {
        bool _v338743;
        if (((((*this).name) == (other.name)))) {
          _v338743 = ((((*this).comment) == (other.comment)));
        } else {
          _v338743 = false;
        }
        _v338742 = _v338743;
      } else {
        _v338742 = false;
      }
      return _v338742;
    }
  };
  struct _HashREGION {
    typedef TPCH_Store::REGION argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code338744 = 0;
      int _hash_code338745 = 0;
      _hash_code338745 = (std::hash<int >()((x.regionkey)));
      _hash_code338744 = ((_hash_code338744 * 31) ^ (_hash_code338745));
      _hash_code338745 = (std::hash<std::string >()((x.name)));
      _hash_code338744 = ((_hash_code338744 * 31) ^ (_hash_code338745));
      _hash_code338745 = (std::hash<std::string >()((x.comment)));
      _hash_code338744 = ((_hash_code338744 * 31) ^ (_hash_code338745));
      return _hash_code338744;
    }
  };
  struct _Type338676 {
    char _0;
    char _1;
    inline _Type338676() { }
    inline _Type338676(char __0, char __1) : _0(::std::move(__0)), _1(::std::move(__1)) { }
    inline bool operator==(const _Type338676& other) const {
      bool _v338746;
      if (((((*this)._0) == (other._0)))) {
        _v338746 = ((((*this)._1) == (other._1)));
      } else {
        _v338746 = false;
      }
      return _v338746;
    }
  };
  struct _Hash_Type338676 {
    typedef TPCH_Store::_Type338676 argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code338747 = 0;
      int _hash_code338748 = 0;
      _hash_code338748 = (std::hash<char >()((x._0)));
      _hash_code338747 = ((_hash_code338747 * 31) ^ (_hash_code338748));
      _hash_code338748 = (std::hash<char >()((x._1)));
      _hash_code338747 = ((_hash_code338747 * 31) ^ (_hash_code338748));
      return _hash_code338747;
    }
  };
protected:
  std::vector< _Type338676  > _var16312;
  std::vector< LINEITEM  > _var8585;
  std::vector< _Type338676  > _var99701;
  std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > _var74137;
  std::unordered_map< _Type338676 , bool , _Hash_Type338676 > _var252302;
  std::vector< LINEITEM  > _var207705;
  std::vector< LINEITEM  > _var316039;
public:
  inline TPCH_Store() {
    std::vector< _Type338676  > _var338749 = (std::vector< _Type338676  > ());
    std::unordered_set< _Type338676 , _Hash_Type338676 > _distinct_elems338751 = (std::unordered_set< _Type338676 , _Hash_Type338676 > ());
    _var16312 = std::move(_var338749);
    _var8585 = (std::vector< LINEITEM  > ());
    std::vector< _Type338676  > _var338754 = (std::vector< _Type338676  > ());
    _var99701 = std::move(_var338754);
    std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > _map338758 = (std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > ());
    _var74137 = std::move(_map338758);
    std::unordered_map< _Type338676 , bool , _Hash_Type338676 > _map338764 = (std::unordered_map< _Type338676 , bool , _Hash_Type338676 > ());
    std::unordered_set< _Type338676 , _Hash_Type338676 > _distinct_elems338766 = (std::unordered_set< _Type338676 , _Hash_Type338676 > ());
    _var252302 = std::move(_map338764);
    std::vector< LINEITEM  > _var338769 = (std::vector< LINEITEM  > ());
    _var207705 = std::move(_var338769);
    std::vector< LINEITEM  > _var338772 = (std::vector< LINEITEM  > ());
    _var316039 = std::move(_var338772);
  }
  explicit inline TPCH_Store(std::vector< LINEITEM  > lineitem, std::vector< ORDERS  > orders, std::vector< PART  > part, std::vector< CUSTOMER  > customer, std::vector< SUPPLIER  > supplier, std::vector< PARTSUPP  > partsupp, std::vector< NATION  > nation, std::vector< REGION  > region) {
    std::vector< _Type338676  > _var338777 = (std::vector< _Type338676  > ());
    std::unordered_set< _Type338676 , _Hash_Type338676 > _distinct_elems338779 = (std::unordered_set< _Type338676 , _Hash_Type338676 > ());
    for (LINEITEM _l338781 : lineitem) {
      if (((_l338781.shipdate) <= 0)) {
        {
          {
            _Type338676 _var338778 = (_Type338676((_l338781.returnflag), (_l338781.linestatus)));
            if ((!((_distinct_elems338779.find(_var338778) != _distinct_elems338779.end())))) {
              _var338777.push_back(_var338778);
              _distinct_elems338779.insert(_var338778);
            }
          }
        }
      }
    }
    _var16312 = std::move(_var338777);
    _var8585 = lineitem;
    std::vector< _Type338676  > _var338782 = (std::vector< _Type338676  > ());
    for (LINEITEM _l338785 : lineitem) {
      if (((_l338785.shipdate) <= 0)) {
        {
          {
            _var338782.push_back((_Type338676((_l338785.returnflag), (_l338785.linestatus))));
          }
        }
      }
    }
    _var99701 = std::move(_var338782);
    std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > _map338786 = (std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > ());
    for (LINEITEM _l338788 : lineitem) {
      {
        int _var70841 = (_l338788.orderkey);
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator338792 = _map338786.find(_var70841);
        if ((_map_iterator338792 == _map338786.end())) {
          _map_iterator338792 = (_map338786.emplace(_var70841, (std::vector< LINEITEM  > ())).first);
        }
        std::vector< LINEITEM  > &_v338787 = _map_iterator338792->second;

        std::vector< LINEITEM  > _var338789 = (std::vector< LINEITEM  > ());
        for (LINEITEM _l338791 : lineitem) {
          if ((((_l338791.orderkey) == _var70841))) {
            {
              _var338789.push_back(_l338791);
            }
          }
        }
        _v338787 = std::move(_var338789);
      }
    }
    _var74137 = std::move(_map338786);
    std::unordered_map< _Type338676 , bool , _Hash_Type338676 > _map338793 = (std::unordered_map< _Type338676 , bool , _Hash_Type338676 > ());
    std::unordered_set< _Type338676 , _Hash_Type338676 > _distinct_elems338795 = (std::unordered_set< _Type338676 , _Hash_Type338676 > ());
    for (LINEITEM _l338797 : lineitem) {
      if (((_l338797.shipdate) <= 0)) {
        {
          {
            _Type338676 _var147117 = (_Type338676((_l338797.returnflag), (_l338797.linestatus)));
            if ((!((_distinct_elems338795.find(_var147117) != _distinct_elems338795.end())))) {
              std::unordered_map< _Type338676 , bool , _Hash_Type338676 >::iterator _map_iterator338798 = _map338793.find(_var147117);
              if ((_map_iterator338798 == _map338793.end())) {
                _map_iterator338798 = (_map338793.emplace(_var147117, false).first);
              }
              bool &_v338794 = _map_iterator338798->second;

              _v338794 = true;
              _distinct_elems338795.insert(_var147117);
            }
          }
        }
      }
    }
    _var252302 = std::move(_map338793);
    std::vector< LINEITEM  > _var338799 = (std::vector< LINEITEM  > ());
    for (LINEITEM _l338801 : lineitem) {
      if (((_l338801.shipdate) <= 0)) {
        {
          _var338799.push_back(_l338801);
        }
      }
    }
    _var207705 = std::move(_var338799);
    std::vector< LINEITEM  > _var338802 = (std::vector< LINEITEM  > ());
    for (LINEITEM __var293232338804 : lineitem) {
      std::unordered_map< LINEITEM , bool , _HashLINEITEM > _map338805 = (std::unordered_map< LINEITEM , bool , _HashLINEITEM > ());
      for (LINEITEM _var293233 : lineitem) {
        std::unordered_map< LINEITEM , bool , _HashLINEITEM >::iterator _map_iterator338807 = _map338805.find(_var293233);
        if ((_map_iterator338807 == _map338805.end())) {
          _map_iterator338807 = (_map338805.emplace(_var293233, false).first);
        }
        bool &_v338806 = _map_iterator338807->second;

        _v338806 = true;
      }
      if ((!(std::move(_map338805).find(__var293232338804) != std::move(_map338805).end()))) {
        {
          _var338802.push_back(__var293232338804);
        }
      }
    }
    _var316039 = std::move(_var338802);
  }
  TPCH_Store(const TPCH_Store& other) = delete;
  template <class F>
  inline void issueQuery(const F& _callback) {
    for (_Type338676 _x338808 : _var16312) {
      _callback(_x338808);
    }
  }
  inline void addLineitem (int orderkey, int partkey, int suppkey, int linenumber, float quantity, float extendedprice, float discount, float tax, char returnflag, char linestatus, int shipdate, int commitdate, int receiptdate, std::string shipinstruct, std::string shipmode, std::string comment) {
    std::vector< int  > _var338809 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram338811 = (std::unordered_map< int , int , std::hash<int > > ());
    std::vector< LINEITEM  > _var338815 = (std::vector< LINEITEM  > ());
    for (LINEITEM _var338816 : _var8585) {
      _var338815.push_back(_var338816);
    }
    {
      _var338815.push_back((LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment)));
    }
    std::vector< LINEITEM  > __var173473338817 = std::move(_var338815);
    std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > _map338818 = (std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > ());
    for (LINEITEM _l338820 : __var173473338817) {
      {
        int _var70841 = (_l338820.orderkey);
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator338932 = _map338818.find(_var70841);
        if ((_map_iterator338932 == _map338818.end())) {
          _map_iterator338932 = (_map338818.emplace(_var70841, (std::vector< LINEITEM  > ())).first);
        }
        std::vector< LINEITEM  > &_v338819 = _map_iterator338932->second;

        std::vector< LINEITEM  > _var338821 = (std::vector< LINEITEM  > ());
        for (LINEITEM _l338823 : __var173473338817) {
          if ((((_l338823.orderkey) == _var70841))) {
            {
              _var338821.push_back(_l338823);
            }
          }
        }
        _v338819 = std::move(_var338821);
      }
    }
    for (const auto & _var338933 : std::move(_map338818)) {
      int _x338812 = (_var338933.first);
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator338934 = _histogram338811.find(_x338812);
      if ((_map_iterator338934 == _histogram338811.end())) {
        _map_iterator338934 = (_histogram338811.emplace(_x338812, 0).first);
      }
      int &_count338813 = _map_iterator338934->second;

      _count338813 = (_count338813 + 1);
    }
    for (const auto & _var338935 : _var74137) {
      int _var338810 = (_var338935.first);
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator338936 = (_histogram338811.find(_var338810));
      int _v338937;
      if ((_map_iterator338936 == _histogram338811.end())) {
        _v338937 = 0;
      } else {
        _v338937 = (_map_iterator338936->second);
      }
      if ((_v338937 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator338938 = _histogram338811.find(_var338810);
        if ((_map_iterator338938 == _histogram338811.end())) {
          _map_iterator338938 = (_histogram338811.emplace(_var338810, 0).first);
        }
        int &_count338814 = _map_iterator338938->second;

        _count338814 = (_count338814 - 1);
      } else {
        _var338809.push_back(_var338810);
      }
    }
    std::vector< int  > _var338659 = std::move(_var338809);
    std::vector< int  > _var338824 = (std::vector< int  > ());
    std::vector< LINEITEM  > _var338853 = (std::vector< LINEITEM  > ());
    for (LINEITEM _var338854 : _var8585) {
      _var338853.push_back(_var338854);
    }
    {
      _var338853.push_back((LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment)));
    }
    std::vector< LINEITEM  > __var223018338855 = std::move(_var338853);
    std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > _map338856 = (std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > ());
    for (LINEITEM _l338858 : __var223018338855) {
      {
        int _var70841 = (_l338858.orderkey);
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator338939 = _map338856.find(_var70841);
        if ((_map_iterator338939 == _map338856.end())) {
          _map_iterator338939 = (_map338856.emplace(_var70841, (std::vector< LINEITEM  > ())).first);
        }
        std::vector< LINEITEM  > &_v338857 = _map_iterator338939->second;

        std::vector< LINEITEM  > _var338859 = (std::vector< LINEITEM  > ());
        for (LINEITEM _l338861 : __var223018338855) {
          if ((((_l338861.orderkey) == _var70841))) {
            {
              _var338859.push_back(_l338861);
            }
          }
        }
        _v338857 = std::move(_var338859);
      }
    }
    for (const auto & _var338940 : std::move(_map338856)) {
      int __var157827338826 = (_var338940.first);
      bool _conditional_result338827 = false;
      bool _found338828 = false;
      {
        for (LINEITEM _l338831 : _var8585) {
          {
            if ((((_l338831.orderkey) == __var157827338826))) {
              _found338828 = true;
              goto _label338941;
            }
          }
        }
      }
_label338941:
      if (_found338828) {
        std::vector< LINEITEM  > _var338832 = (std::vector< LINEITEM  > ());
        for (LINEITEM _l338834 : _var8585) {
          if ((((_l338834.orderkey) == __var157827338826))) {
            {
              _var338832.push_back(_l338834);
            }
          }
        }
        std::vector< LINEITEM  > _var338835 = (std::vector< LINEITEM  > ());
        for (LINEITEM _var338836 : _var8585) {
          _var338835.push_back(_var338836);
        }
        {
          _var338835.push_back((LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment)));
        }
        std::vector< LINEITEM  > __var223021338837 = std::move(_var338835);
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > _map338838 = (std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > ());
        for (LINEITEM _l338840 : __var223021338837) {
          {
            int _var70841 = (_l338840.orderkey);
            std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator338942 = _map338838.find(_var70841);
            if ((_map_iterator338942 == _map338838.end())) {
              _map_iterator338942 = (_map338838.emplace(_var70841, (std::vector< LINEITEM  > ())).first);
            }
            std::vector< LINEITEM  > &_v338839 = _map_iterator338942->second;

            std::vector< LINEITEM  > _var338841 = (std::vector< LINEITEM  > ());
            for (LINEITEM _l338843 : __var223021338837) {
              if ((((_l338843.orderkey) == _var70841))) {
                {
                  _var338841.push_back(_l338843);
                }
              }
            }
            _v338839 = std::move(_var338841);
          }
        }
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::const_iterator _map_iterator338943 = (std::move(_map338838).find(__var157827338826));
        std::vector< LINEITEM  > _v338944;
        if ((_map_iterator338943 == std::move(_map338838).end())) {
          _v338944 = (std::vector< LINEITEM  > ());
        } else {
          _v338944 = (_map_iterator338943->second);
        }
        _conditional_result338827 = ((std::move(_var338832) == _v338944));
      } else {
        std::vector< LINEITEM  > _var338844 = (std::vector< LINEITEM  > ());
        for (LINEITEM _var338845 : _var8585) {
          _var338844.push_back(_var338845);
        }
        {
          _var338844.push_back((LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment)));
        }
        std::vector< LINEITEM  > __var223021338846 = std::move(_var338844);
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > _map338847 = (std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > ());
        for (LINEITEM _l338849 : __var223021338846) {
          {
            int _var70841 = (_l338849.orderkey);
            std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator338945 = _map338847.find(_var70841);
            if ((_map_iterator338945 == _map338847.end())) {
              _map_iterator338945 = (_map338847.emplace(_var70841, (std::vector< LINEITEM  > ())).first);
            }
            std::vector< LINEITEM  > &_v338848 = _map_iterator338945->second;

            std::vector< LINEITEM  > _var338850 = (std::vector< LINEITEM  > ());
            for (LINEITEM _l338852 : __var223021338846) {
              if ((((_l338852.orderkey) == _var70841))) {
                {
                  _var338850.push_back(_l338852);
                }
              }
            }
            _v338848 = std::move(_var338850);
          }
        }
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::const_iterator _map_iterator338946 = (std::move(_map338847).find(__var157827338826));
        std::vector< LINEITEM  > _v338947;
        if ((_map_iterator338946 == std::move(_map338847).end())) {
          _v338947 = (std::vector< LINEITEM  > ());
        } else {
          _v338947 = (_map_iterator338946->second);
        }
        _conditional_result338827 = (((std::vector< LINEITEM  > ()) == _v338947));
      }
      bool _v338948;
      if ((!(_var74137.find(__var157827338826) != _var74137.end()))) {
        _v338948 = true;
      } else {
        _v338948 = (!(_conditional_result338827));
      }
      if (_v338948) {
        {
          _var338824.push_back(__var157827338826);
        }
      }
    }
    std::vector< int  > _var338660 = std::move(_var338824);
    std::vector< LINEITEM  > _var338862 = (std::vector< LINEITEM  > ());
    std::unordered_map< LINEITEM , int , _HashLINEITEM > _histogram338864 = (std::unordered_map< LINEITEM , int , _HashLINEITEM > ());
    for (LINEITEM _x338865 : _var207705) {
      std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator338949 = _histogram338864.find(_x338865);
      if ((_map_iterator338949 == _histogram338864.end())) {
        _map_iterator338949 = (_histogram338864.emplace(_x338865, 0).first);
      }
      int &_count338866 = _map_iterator338949->second;

      _count338866 = (_count338866 + 1);
    }
    for (LINEITEM _var338863 : _var207705) {
      std::unordered_map< LINEITEM , int , _HashLINEITEM >::const_iterator _map_iterator338950 = (_histogram338864.find(_var338863));
      int _v338951;
      if ((_map_iterator338950 == _histogram338864.end())) {
        _v338951 = 0;
      } else {
        _v338951 = (_map_iterator338950->second);
      }
      if ((_v338951 > 0)) {
        std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator338952 = _histogram338864.find(_var338863);
        if ((_map_iterator338952 == _histogram338864.end())) {
          _map_iterator338952 = (_histogram338864.emplace(_var338863, 0).first);
        }
        int &_count338867 = _map_iterator338952->second;

        _count338867 = (_count338867 - 1);
      } else {
        _var338862.push_back(_var338863);
      }
    }
    if ((shipdate <= 0)) {
      {
        LINEITEM _var338863 = (LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment));
        std::unordered_map< LINEITEM , int , _HashLINEITEM >::const_iterator _map_iterator338953 = (_histogram338864.find(_var338863));
        int _v338954;
        if ((_map_iterator338953 == _histogram338864.end())) {
          _v338954 = 0;
        } else {
          _v338954 = (_map_iterator338953->second);
        }
        if ((_v338954 > 0)) {
          std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator338955 = _histogram338864.find(_var338863);
          if ((_map_iterator338955 == _histogram338864.end())) {
            _map_iterator338955 = (_histogram338864.emplace(_var338863, 0).first);
          }
          int &_count338867 = _map_iterator338955->second;

          _count338867 = (_count338867 - 1);
        } else {
          _var338862.push_back(_var338863);
        }
      }
    }
    std::vector< LINEITEM  > _var338661 = std::move(_var338862);
    std::vector< _Type338676  > _var338868 = (std::vector< _Type338676  > ());
    if ((shipdate <= 0)) {
      {
        LINEITEM _l338871 = (LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment));
        {
          _Type338676 __var147116338870 = (_Type338676((_l338871.returnflag), (_l338871.linestatus)));
          if ((!(_var252302.find(__var147116338870) != _var252302.end()))) {
            {
              _var338868.push_back(__var147116338870);
            }
          }
        }
      }
    }
    std::vector< _Type338676  > _var338662 = std::move(_var338868);
    for (_Type338676 _var267699 : _var338662) {
      std::unordered_map< _Type338676 , bool , _Hash_Type338676 >::iterator _map_iterator338956 = _var252302.find(_var267699);
      if ((_map_iterator338956 == _var252302.end())) {
        _map_iterator338956 = (_var252302.emplace(_var267699, false).first);
      }
      bool &_var267700 = _map_iterator338956->second;

      bool _conditional_result338872 = false;
      bool _found338873 = false;
      {
        for (_Type338676 _x338874 : _var99701) {
          if (((_x338874 == _var267699))) {
            _found338873 = true;
            goto _label338957;
          }
        }
        if ((shipdate <= 0)) {
          {
            LINEITEM _l338876 = (LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment));
            {
              if ((((_Type338676((_l338876.returnflag), (_l338876.linestatus))) == _var267699))) {
                _found338873 = true;
                goto _label338957;
              }
            }
          }
        }
      }
_label338957:
      if (_found338873) {
        _conditional_result338872 = true;
      } else {
        _conditional_result338872 = false;
      }
      _var267700 = _conditional_result338872;
    }
    if ((shipdate <= 0)) {
      {
        {
          _var99701.push_back((_Type338676(returnflag, linestatus)));
        }
      }
    }
    if ((shipdate <= 0)) {
      {
        LINEITEM _l338879 = (LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment));
        {
          _Type338676 __var147116338878 = (_Type338676((_l338879.returnflag), (_l338879.linestatus)));
          if ((!(_var252302.find(__var147116338878) != _var252302.end()))) {
            {
              _var16312.push_back(__var147116338878);
            }
          }
        }
      }
    }
    for (LINEITEM _var302626 : _var338661) {
      _var207705.push_back(_var302626);
    }
    {
      _var8585.push_back((LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment)));
    }
    for (int _var157827 : _var338659) {
      _var74137.erase(_var157827);
    }
    for (int _var157827 : _var338660) {
      std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator338958 = _var74137.find(_var157827);
      if ((_map_iterator338958 == _var74137.end())) {
        _map_iterator338958 = (_var74137.emplace(_var157827, (std::vector< LINEITEM  > ())).first);
      }
      std::vector< LINEITEM  > &_var157828 = _map_iterator338958->second;

      if (true) {
        std::unordered_map< LINEITEM , int , _HashLINEITEM > _histogram338880 = (std::unordered_map< LINEITEM , int , _HashLINEITEM > ());
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > _map338884 = (std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > ());
        for (LINEITEM _l338886 : _var8585) {
          {
            int _var70841 = (_l338886.orderkey);
            std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator338959 = _map338884.find(_var70841);
            if ((_map_iterator338959 == _map338884.end())) {
              _map_iterator338959 = (_map338884.emplace(_var70841, (std::vector< LINEITEM  > ())).first);
            }
            std::vector< LINEITEM  > &_v338885 = _map_iterator338959->second;

            std::vector< LINEITEM  > _var338887 = (std::vector< LINEITEM  > ());
            for (LINEITEM _l338889 : _var8585) {
              if ((((_l338889.orderkey) == _var70841))) {
                {
                  _var338887.push_back(_l338889);
                }
              }
            }
            {
              LINEITEM _l338889 = (LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment));
              if ((((_l338889.orderkey) == _var70841))) {
                {
                  _var338887.push_back(_l338889);
                }
              }
            }
            _v338885 = std::move(_var338887);
          }
        }
        {
          {
            int _var70841 = ((LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment)).orderkey);
            std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator338960 = _map338884.find(_var70841);
            if ((_map_iterator338960 == _map338884.end())) {
              _map_iterator338960 = (_map338884.emplace(_var70841, (std::vector< LINEITEM  > ())).first);
            }
            std::vector< LINEITEM  > &_v338885 = _map_iterator338960->second;

            std::vector< LINEITEM  > _var338887 = (std::vector< LINEITEM  > ());
            for (LINEITEM _l338889 : _var8585) {
              if ((((_l338889.orderkey) == _var70841))) {
                {
                  _var338887.push_back(_l338889);
                }
              }
            }
            {
              LINEITEM _l338889 = (LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment));
              if ((((_l338889.orderkey) == _var70841))) {
                {
                  _var338887.push_back(_l338889);
                }
              }
            }
            _v338885 = std::move(_var338887);
          }
        }
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::const_iterator _map_iterator338961 = (std::move(_map338884).find(_var157827));
        std::vector< LINEITEM  > _v338962;
        if ((_map_iterator338961 == std::move(_map338884).end())) {
          _v338962 = (std::vector< LINEITEM  > ());
        } else {
          _v338962 = (_map_iterator338961->second);
        }
        for (LINEITEM _x338881 : _v338962) {
          std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator338963 = _histogram338880.find(_x338881);
          if ((_map_iterator338963 == _histogram338880.end())) {
            _map_iterator338963 = (_histogram338880.emplace(_x338881, 0).first);
          }
          int &_count338882 = _map_iterator338963->second;

          _count338882 = (_count338882 + 1);
        }
        for (LINEITEM _l338890 : _var8585) {
          if ((((_l338890.orderkey) == _var157827))) {
            {
              std::unordered_map< LINEITEM , int , _HashLINEITEM >::const_iterator _map_iterator338964 = (_histogram338880.find(_l338890));
              int _v338965;
              if ((_map_iterator338964 == _histogram338880.end())) {
                _v338965 = 0;
              } else {
                _v338965 = (_map_iterator338964->second);
              }
              if ((_v338965 > 0)) {
                std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator338966 = _histogram338880.find(_l338890);
                if ((_map_iterator338966 == _histogram338880.end())) {
                  _map_iterator338966 = (_histogram338880.emplace(_l338890, 0).first);
                }
                int &_count338883 = _map_iterator338966->second;

                _count338883 = (_count338883 - 1);
              } else {
                auto _it338967(::std::find(_var157828.begin(), _var157828.end(), _l338890));
                if (_it338967 != _var157828.end()) { _var157828.erase(_it338967); }
              }
            }
          }
        }
      } else {
        std::unordered_map< LINEITEM , int , _HashLINEITEM > _histogram338891 = (std::unordered_map< LINEITEM , int , _HashLINEITEM > ());
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > _map338895 = (std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > ());
        for (LINEITEM _l338897 : _var8585) {
          {
            int _var70841 = (_l338897.orderkey);
            std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator338968 = _map338895.find(_var70841);
            if ((_map_iterator338968 == _map338895.end())) {
              _map_iterator338968 = (_map338895.emplace(_var70841, (std::vector< LINEITEM  > ())).first);
            }
            std::vector< LINEITEM  > &_v338896 = _map_iterator338968->second;

            std::vector< LINEITEM  > _var338898 = (std::vector< LINEITEM  > ());
            for (LINEITEM _l338900 : _var8585) {
              if ((((_l338900.orderkey) == _var70841))) {
                {
                  _var338898.push_back(_l338900);
                }
              }
            }
            {
              LINEITEM _l338900 = (LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment));
              if ((((_l338900.orderkey) == _var70841))) {
                {
                  _var338898.push_back(_l338900);
                }
              }
            }
            _v338896 = std::move(_var338898);
          }
        }
        {
          {
            int _var70841 = ((LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment)).orderkey);
            std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator338969 = _map338895.find(_var70841);
            if ((_map_iterator338969 == _map338895.end())) {
              _map_iterator338969 = (_map338895.emplace(_var70841, (std::vector< LINEITEM  > ())).first);
            }
            std::vector< LINEITEM  > &_v338896 = _map_iterator338969->second;

            std::vector< LINEITEM  > _var338898 = (std::vector< LINEITEM  > ());
            for (LINEITEM _l338900 : _var8585) {
              if ((((_l338900.orderkey) == _var70841))) {
                {
                  _var338898.push_back(_l338900);
                }
              }
            }
            {
              LINEITEM _l338900 = (LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment));
              if ((((_l338900.orderkey) == _var70841))) {
                {
                  _var338898.push_back(_l338900);
                }
              }
            }
            _v338896 = std::move(_var338898);
          }
        }
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::const_iterator _map_iterator338970 = (std::move(_map338895).find(_var157827));
        std::vector< LINEITEM  > _v338971;
        if ((_map_iterator338970 == std::move(_map338895).end())) {
          _v338971 = (std::vector< LINEITEM  > ());
        } else {
          _v338971 = (_map_iterator338970->second);
        }
        for (LINEITEM _x338892 : _v338971) {
          std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator338972 = _histogram338891.find(_x338892);
          if ((_map_iterator338972 == _histogram338891.end())) {
            _map_iterator338972 = (_histogram338891.emplace(_x338892, 0).first);
          }
          int &_count338893 = _map_iterator338972->second;

          _count338893 = (_count338893 + 1);
        }
      }
      bool _found338901 = false;
      {
        for (LINEITEM _l338904 : _var8585) {
          {
            if ((((_l338904.orderkey) == _var157827))) {
              _found338901 = true;
              goto _label338973;
            }
          }
        }
      }
_label338973:
      if (_found338901) {
        std::unordered_map< LINEITEM , int , _HashLINEITEM > _histogram338905 = (std::unordered_map< LINEITEM , int , _HashLINEITEM > ());
        for (LINEITEM _l338909 : _var8585) {
          if ((((_l338909.orderkey) == _var157827))) {
            {
              std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator338974 = _histogram338905.find(_l338909);
              if ((_map_iterator338974 == _histogram338905.end())) {
                _map_iterator338974 = (_histogram338905.emplace(_l338909, 0).first);
              }
              int &_count338907 = _map_iterator338974->second;

              _count338907 = (_count338907 + 1);
            }
          }
        }
        std::vector< LINEITEM  > _var338910 = (std::vector< LINEITEM  > ());
        for (LINEITEM _var338911 : _var8585) {
          _var338910.push_back(_var338911);
        }
        {
          _var338910.push_back((LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment)));
        }
        std::vector< LINEITEM  > __var186151338912 = std::move(_var338910);
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > _map338913 = (std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > ());
        for (LINEITEM _l338915 : __var186151338912) {
          {
            int _var70841 = (_l338915.orderkey);
            std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator338975 = _map338913.find(_var70841);
            if ((_map_iterator338975 == _map338913.end())) {
              _map_iterator338975 = (_map338913.emplace(_var70841, (std::vector< LINEITEM  > ())).first);
            }
            std::vector< LINEITEM  > &_v338914 = _map_iterator338975->second;

            std::vector< LINEITEM  > _var338916 = (std::vector< LINEITEM  > ());
            for (LINEITEM _l338918 : __var186151338912) {
              if ((((_l338918.orderkey) == _var70841))) {
                {
                  _var338916.push_back(_l338918);
                }
              }
            }
            _v338914 = std::move(_var338916);
          }
        }
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::const_iterator _map_iterator338976 = (std::move(_map338913).find(_var157827));
        std::vector< LINEITEM  > _v338977;
        if ((_map_iterator338976 == std::move(_map338913).end())) {
          _v338977 = (std::vector< LINEITEM  > ());
        } else {
          _v338977 = (_map_iterator338976->second);
        }
        for (LINEITEM _var172819 : _v338977) {
          std::unordered_map< LINEITEM , int , _HashLINEITEM >::const_iterator _map_iterator338978 = (_histogram338905.find(_var172819));
          int _v338979;
          if ((_map_iterator338978 == _histogram338905.end())) {
            _v338979 = 0;
          } else {
            _v338979 = (_map_iterator338978->second);
          }
          if ((_v338979 > 0)) {
            std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator338980 = _histogram338905.find(_var172819);
            if ((_map_iterator338980 == _histogram338905.end())) {
              _map_iterator338980 = (_histogram338905.emplace(_var172819, 0).first);
            }
            int &_count338908 = _map_iterator338980->second;

            _count338908 = (_count338908 - 1);
          } else {
            _var157828.push_back(_var172819);
          }
        }
      } else {
        std::unordered_map< LINEITEM , int , _HashLINEITEM > _histogram338919 = (std::unordered_map< LINEITEM , int , _HashLINEITEM > ());
        std::vector< LINEITEM  > _var338923 = (std::vector< LINEITEM  > ());
        for (LINEITEM _var338924 : _var8585) {
          _var338923.push_back(_var338924);
        }
        {
          _var338923.push_back((LINEITEM (orderkey, partkey, suppkey, linenumber, quantity, extendedprice, discount, tax, returnflag, linestatus, shipdate, commitdate, receiptdate, shipinstruct, shipmode, comment)));
        }
        std::vector< LINEITEM  > __var186151338925 = std::move(_var338923);
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > _map338926 = (std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > ());
        for (LINEITEM _l338928 : __var186151338925) {
          {
            int _var70841 = (_l338928.orderkey);
            std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator338981 = _map338926.find(_var70841);
            if ((_map_iterator338981 == _map338926.end())) {
              _map_iterator338981 = (_map338926.emplace(_var70841, (std::vector< LINEITEM  > ())).first);
            }
            std::vector< LINEITEM  > &_v338927 = _map_iterator338981->second;

            std::vector< LINEITEM  > _var338929 = (std::vector< LINEITEM  > ());
            for (LINEITEM _l338931 : __var186151338925) {
              if ((((_l338931.orderkey) == _var70841))) {
                {
                  _var338929.push_back(_l338931);
                }
              }
            }
            _v338927 = std::move(_var338929);
          }
        }
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::const_iterator _map_iterator338982 = (std::move(_map338926).find(_var157827));
        std::vector< LINEITEM  > _v338983;
        if ((_map_iterator338982 == std::move(_map338926).end())) {
          _v338983 = (std::vector< LINEITEM  > ());
        } else {
          _v338983 = (_map_iterator338982->second);
        }
        for (LINEITEM _var172819 : _v338983) {
          std::unordered_map< LINEITEM , int , _HashLINEITEM >::const_iterator _map_iterator338984 = (_histogram338919.find(_var172819));
          int _v338985;
          if ((_map_iterator338984 == _histogram338919.end())) {
            _v338985 = 0;
          } else {
            _v338985 = (_map_iterator338984->second);
          }
          if ((_v338985 > 0)) {
            std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator338986 = _histogram338919.find(_var172819);
            if ((_map_iterator338986 == _histogram338919.end())) {
              _map_iterator338986 = (_histogram338919.emplace(_var172819, 0).first);
            }
            int &_count338922 = _map_iterator338986->second;

            _count338922 = (_count338922 - 1);
          } else {
            _var157828.push_back(_var172819);
          }
        }
      }
    }
  }
  inline void deleteOldSales (int orderkey) {
    std::vector< _Type338676  > _var338987 = (std::vector< _Type338676  > ());
    std::unordered_map< _Type338676 , int , _Hash_Type338676 > _histogram338989 = (std::unordered_map< _Type338676 , int , _Hash_Type338676 > ());
    for (LINEITEM __var163410338995 : _var8585) {
      if ((!((((__var163410338995.orderkey) == orderkey))))) {
        {
          if (((__var163410338995.shipdate) <= 0)) {
            {
              {
                std::unordered_map< _Type338676 , int , _Hash_Type338676 >::iterator _map_iterator339094 = _histogram338989.find((_Type338676((__var163410338995.returnflag), (__var163410338995.linestatus))));
                if ((_map_iterator339094 == _histogram338989.end())) {
                  _map_iterator339094 = (_histogram338989.emplace((_Type338676((__var163410338995.returnflag), (__var163410338995.linestatus))), 0).first);
                }
                int &_count338991 = _map_iterator339094->second;

                _count338991 = (_count338991 + 1);
              }
            }
          }
        }
      }
    }
    for (_Type338676 _var338988 : _var99701) {
      std::unordered_map< _Type338676 , int , _Hash_Type338676 >::const_iterator _map_iterator339095 = (_histogram338989.find(_var338988));
      int _v339096;
      if ((_map_iterator339095 == _histogram338989.end())) {
        _v339096 = 0;
      } else {
        _v339096 = (_map_iterator339095->second);
      }
      if ((_v339096 > 0)) {
        std::unordered_map< _Type338676 , int , _Hash_Type338676 >::iterator _map_iterator339097 = _histogram338989.find(_var338988);
        if ((_map_iterator339097 == _histogram338989.end())) {
          _map_iterator339097 = (_histogram338989.emplace(_var338988, 0).first);
        }
        int &_count338992 = _map_iterator339097->second;

        _count338992 = (_count338992 - 1);
      } else {
        _var338987.push_back(_var338988);
      }
    }
    std::vector< _Type338676  > _var338663 = std::move(_var338987);
    std::vector< _Type338676  > _var338996 = (std::vector< _Type338676  > ());
    std::unordered_map< _Type338676 , int , _Hash_Type338676 > _histogram338998 = (std::unordered_map< _Type338676 , int , _Hash_Type338676 > ());
    for (LINEITEM __var22124339003 : _var207705) {
      if ((!((((__var22124339003.orderkey) == orderkey))))) {
        {
          {
            std::unordered_map< _Type338676 , int , _Hash_Type338676 >::iterator _map_iterator339098 = _histogram338998.find((_Type338676((__var22124339003.returnflag), (__var22124339003.linestatus))));
            if ((_map_iterator339098 == _histogram338998.end())) {
              _map_iterator339098 = (_histogram338998.emplace((_Type338676((__var22124339003.returnflag), (__var22124339003.linestatus))), 0).first);
            }
            int &_count339000 = _map_iterator339098->second;

            _count339000 = (_count339000 + 1);
          }
        }
      }
    }
    for (_Type338676 _var338997 : _var16312) {
      std::unordered_map< _Type338676 , int , _Hash_Type338676 >::const_iterator _map_iterator339099 = (_histogram338998.find(_var338997));
      int _v339100;
      if ((_map_iterator339099 == _histogram338998.end())) {
        _v339100 = 0;
      } else {
        _v339100 = (_map_iterator339099->second);
      }
      if ((_v339100 > 0)) {
        std::unordered_map< _Type338676 , int , _Hash_Type338676 >::iterator _map_iterator339101 = _histogram338998.find(_var338997);
        if ((_map_iterator339101 == _histogram338998.end())) {
          _map_iterator339101 = (_histogram338998.emplace(_var338997, 0).first);
        }
        int &_count339001 = _map_iterator339101->second;

        _count339001 = (_count339001 - 1);
      } else {
        _var338996.push_back(_var338997);
      }
    }
    std::vector< _Type338676  > _var338664 = std::move(_var338996);
    std::vector< LINEITEM  > _var339004 = (std::vector< LINEITEM  > ());
    std::unordered_map< LINEITEM , int , _HashLINEITEM > _histogram339006 = (std::unordered_map< LINEITEM , int , _HashLINEITEM > ());
    std::unordered_map< LINEITEM , int , _HashLINEITEM > _histogram339011 = (std::unordered_map< LINEITEM , int , _HashLINEITEM > ());
    for (LINEITEM _l339015 : _var8585) {
      if ((((_l339015.orderkey) == orderkey))) {
        {
          std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator339102 = _histogram339011.find(_l339015);
          if ((_map_iterator339102 == _histogram339011.end())) {
            _map_iterator339102 = (_histogram339011.emplace(_l339015, 0).first);
          }
          int &_count339013 = _map_iterator339102->second;

          _count339013 = (_count339013 + 1);
        }
      }
    }
    for (LINEITEM _l339010 : _var8585) {
      std::unordered_map< LINEITEM , int , _HashLINEITEM >::const_iterator _map_iterator339103 = (_histogram339011.find(_l339010));
      int _v339104;
      if ((_map_iterator339103 == _histogram339011.end())) {
        _v339104 = 0;
      } else {
        _v339104 = (_map_iterator339103->second);
      }
      if ((_v339104 > 0)) {
        std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator339105 = _histogram339011.find(_l339010);
        if ((_map_iterator339105 == _histogram339011.end())) {
          _map_iterator339105 = (_histogram339011.emplace(_l339010, 0).first);
        }
        int &_count339014 = _map_iterator339105->second;

        _count339014 = (_count339014 - 1);
      } else {
        if (((_l339010.shipdate) <= 0)) {
          {
            std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator339106 = _histogram339006.find(_l339010);
            if ((_map_iterator339106 == _histogram339006.end())) {
              _map_iterator339106 = (_histogram339006.emplace(_l339010, 0).first);
            }
            int &_count339008 = _map_iterator339106->second;

            _count339008 = (_count339008 + 1);
          }
        }
      }
    }
    for (LINEITEM _var339005 : _var207705) {
      std::unordered_map< LINEITEM , int , _HashLINEITEM >::const_iterator _map_iterator339107 = (_histogram339006.find(_var339005));
      int _v339108;
      if ((_map_iterator339107 == _histogram339006.end())) {
        _v339108 = 0;
      } else {
        _v339108 = (_map_iterator339107->second);
      }
      if ((_v339108 > 0)) {
        std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator339109 = _histogram339006.find(_var339005);
        if ((_map_iterator339109 == _histogram339006.end())) {
          _map_iterator339109 = (_histogram339006.emplace(_var339005, 0).first);
        }
        int &_count339009 = _map_iterator339109->second;

        _count339009 = (_count339009 - 1);
      } else {
        _var339004.push_back(_var339005);
      }
    }
    std::vector< LINEITEM  > _var338665 = std::move(_var339004);
    std::vector< int  > _var339016 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram339018 = (std::unordered_map< int , int , std::hash<int > > ());
    std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > _map339022 = (std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > ());
    for (LINEITEM __var293232339033 : _var8585) {
      if ((!((((__var293232339033.orderkey) == orderkey))))) {
        {
          {
            int _var70841 = (__var293232339033.orderkey);
            std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator339110 = _map339022.find(_var70841);
            if ((_map_iterator339110 == _map339022.end())) {
              _map_iterator339110 = (_map339022.emplace(_var70841, (std::vector< LINEITEM  > ())).first);
            }
            std::vector< LINEITEM  > &_v339023 = _map_iterator339110->second;

            std::vector< LINEITEM  > _var339025 = (std::vector< LINEITEM  > ());
            std::unordered_map< LINEITEM , int , _HashLINEITEM > _histogram339028 = (std::unordered_map< LINEITEM , int , _HashLINEITEM > ());
            for (LINEITEM _l339032 : _var8585) {
              if ((((_l339032.orderkey) == orderkey))) {
                {
                  std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator339111 = _histogram339028.find(_l339032);
                  if ((_map_iterator339111 == _histogram339028.end())) {
                    _map_iterator339111 = (_histogram339028.emplace(_l339032, 0).first);
                  }
                  int &_count339030 = _map_iterator339111->second;

                  _count339030 = (_count339030 + 1);
                }
              }
            }
            for (LINEITEM _l339027 : _var8585) {
              std::unordered_map< LINEITEM , int , _HashLINEITEM >::const_iterator _map_iterator339112 = (_histogram339028.find(_l339027));
              int _v339113;
              if ((_map_iterator339112 == _histogram339028.end())) {
                _v339113 = 0;
              } else {
                _v339113 = (_map_iterator339112->second);
              }
              if ((_v339113 > 0)) {
                std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator339114 = _histogram339028.find(_l339027);
                if ((_map_iterator339114 == _histogram339028.end())) {
                  _map_iterator339114 = (_histogram339028.emplace(_l339027, 0).first);
                }
                int &_count339031 = _map_iterator339114->second;

                _count339031 = (_count339031 - 1);
              } else {
                if ((((_l339027.orderkey) == _var70841))) {
                  {
                    _var339025.push_back(_l339027);
                  }
                }
              }
            }
            _v339023 = std::move(_var339025);
          }
        }
      }
    }
    for (LINEITEM __var293232339034 : _var316039) {
      if ((!((!((((__var293232339034.orderkey) == orderkey))))))) {
        {
          {
            int _var70841 = (__var293232339034.orderkey);
            std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator339115 = _map339022.find(_var70841);
            if ((_map_iterator339115 == _map339022.end())) {
              _map_iterator339115 = (_map339022.emplace(_var70841, (std::vector< LINEITEM  > ())).first);
            }
            std::vector< LINEITEM  > &_v339023 = _map_iterator339115->second;

            std::vector< LINEITEM  > _var339025 = (std::vector< LINEITEM  > ());
            std::unordered_map< LINEITEM , int , _HashLINEITEM > _histogram339028 = (std::unordered_map< LINEITEM , int , _HashLINEITEM > ());
            for (LINEITEM _l339032 : _var8585) {
              if ((((_l339032.orderkey) == orderkey))) {
                {
                  std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator339116 = _histogram339028.find(_l339032);
                  if ((_map_iterator339116 == _histogram339028.end())) {
                    _map_iterator339116 = (_histogram339028.emplace(_l339032, 0).first);
                  }
                  int &_count339030 = _map_iterator339116->second;

                  _count339030 = (_count339030 + 1);
                }
              }
            }
            for (LINEITEM _l339027 : _var8585) {
              std::unordered_map< LINEITEM , int , _HashLINEITEM >::const_iterator _map_iterator339117 = (_histogram339028.find(_l339027));
              int _v339118;
              if ((_map_iterator339117 == _histogram339028.end())) {
                _v339118 = 0;
              } else {
                _v339118 = (_map_iterator339117->second);
              }
              if ((_v339118 > 0)) {
                std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator339119 = _histogram339028.find(_l339027);
                if ((_map_iterator339119 == _histogram339028.end())) {
                  _map_iterator339119 = (_histogram339028.emplace(_l339027, 0).first);
                }
                int &_count339031 = _map_iterator339119->second;

                _count339031 = (_count339031 - 1);
              } else {
                if ((((_l339027.orderkey) == _var70841))) {
                  {
                    _var339025.push_back(_l339027);
                  }
                }
              }
            }
            _v339023 = std::move(_var339025);
          }
        }
      }
    }
    for (const auto & _var339120 : std::move(_map339022)) {
      int _x339019 = (_var339120.first);
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator339121 = _histogram339018.find(_x339019);
      if ((_map_iterator339121 == _histogram339018.end())) {
        _map_iterator339121 = (_histogram339018.emplace(_x339019, 0).first);
      }
      int &_count339020 = _map_iterator339121->second;

      _count339020 = (_count339020 + 1);
    }
    for (const auto & _var339122 : _var74137) {
      int _var339017 = (_var339122.first);
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator339123 = (_histogram339018.find(_var339017));
      int _v339124;
      if ((_map_iterator339123 == _histogram339018.end())) {
        _v339124 = 0;
      } else {
        _v339124 = (_map_iterator339123->second);
      }
      if ((_v339124 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator339125 = _histogram339018.find(_var339017);
        if ((_map_iterator339125 == _histogram339018.end())) {
          _map_iterator339125 = (_histogram339018.emplace(_var339017, 0).first);
        }
        int &_count339021 = _map_iterator339125->second;

        _count339021 = (_count339021 - 1);
      } else {
        _var339016.push_back(_var339017);
      }
    }
    std::vector< int  > _var338666 = std::move(_var339016);
    std::vector< int  > _var339035 = (std::vector< int  > ());
    std::vector< LINEITEM  > _var339074 = (std::vector< LINEITEM  > ());
    std::unordered_map< LINEITEM , int , _HashLINEITEM > _histogram339076 = (std::unordered_map< LINEITEM , int , _HashLINEITEM > ());
    for (LINEITEM _l339080 : _var8585) {
      if ((((_l339080.orderkey) == orderkey))) {
        {
          std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator339126 = _histogram339076.find(_l339080);
          if ((_map_iterator339126 == _histogram339076.end())) {
            _map_iterator339126 = (_histogram339076.emplace(_l339080, 0).first);
          }
          int &_count339078 = _map_iterator339126->second;

          _count339078 = (_count339078 + 1);
        }
      }
    }
    for (LINEITEM _var339075 : _var8585) {
      std::unordered_map< LINEITEM , int , _HashLINEITEM >::const_iterator _map_iterator339127 = (_histogram339076.find(_var339075));
      int _v339128;
      if ((_map_iterator339127 == _histogram339076.end())) {
        _v339128 = 0;
      } else {
        _v339128 = (_map_iterator339127->second);
      }
      if ((_v339128 > 0)) {
        std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator339129 = _histogram339076.find(_var339075);
        if ((_map_iterator339129 == _histogram339076.end())) {
          _map_iterator339129 = (_histogram339076.emplace(_var339075, 0).first);
        }
        int &_count339079 = _map_iterator339129->second;

        _count339079 = (_count339079 - 1);
      } else {
        _var339074.push_back(_var339075);
      }
    }
    std::vector< LINEITEM  > __var258395339081 = std::move(_var339074);
    std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > _map339082 = (std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > ());
    for (LINEITEM _l339084 : __var258395339081) {
      {
        int _var70841 = (_l339084.orderkey);
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator339130 = _map339082.find(_var70841);
        if ((_map_iterator339130 == _map339082.end())) {
          _map_iterator339130 = (_map339082.emplace(_var70841, (std::vector< LINEITEM  > ())).first);
        }
        std::vector< LINEITEM  > &_v339083 = _map_iterator339130->second;

        std::vector< LINEITEM  > _var339085 = (std::vector< LINEITEM  > ());
        for (LINEITEM _l339087 : __var258395339081) {
          if ((((_l339087.orderkey) == _var70841))) {
            {
              _var339085.push_back(_l339087);
            }
          }
        }
        _v339083 = std::move(_var339085);
      }
    }
    for (const auto & _var339131 : std::move(_map339082)) {
      int __var242931339037 = (_var339131.first);
      bool _conditional_result339038 = false;
      bool _found339039 = false;
      {
        for (LINEITEM _l339042 : _var8585) {
          {
            if ((((_l339042.orderkey) == __var242931339037))) {
              _found339039 = true;
              goto _label339132;
            }
          }
        }
      }
_label339132:
      if (_found339039) {
        std::vector< LINEITEM  > _var339043 = (std::vector< LINEITEM  > ());
        for (LINEITEM _l339045 : _var8585) {
          if ((((_l339045.orderkey) == __var242931339037))) {
            {
              _var339043.push_back(_l339045);
            }
          }
        }
        std::vector< LINEITEM  > _var339046 = (std::vector< LINEITEM  > ());
        std::unordered_map< LINEITEM , int , _HashLINEITEM > _histogram339048 = (std::unordered_map< LINEITEM , int , _HashLINEITEM > ());
        for (LINEITEM _l339052 : _var8585) {
          if ((((_l339052.orderkey) == orderkey))) {
            {
              std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator339133 = _histogram339048.find(_l339052);
              if ((_map_iterator339133 == _histogram339048.end())) {
                _map_iterator339133 = (_histogram339048.emplace(_l339052, 0).first);
              }
              int &_count339050 = _map_iterator339133->second;

              _count339050 = (_count339050 + 1);
            }
          }
        }
        for (LINEITEM _var339047 : _var8585) {
          std::unordered_map< LINEITEM , int , _HashLINEITEM >::const_iterator _map_iterator339134 = (_histogram339048.find(_var339047));
          int _v339135;
          if ((_map_iterator339134 == _histogram339048.end())) {
            _v339135 = 0;
          } else {
            _v339135 = (_map_iterator339134->second);
          }
          if ((_v339135 > 0)) {
            std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator339136 = _histogram339048.find(_var339047);
            if ((_map_iterator339136 == _histogram339048.end())) {
              _map_iterator339136 = (_histogram339048.emplace(_var339047, 0).first);
            }
            int &_count339051 = _map_iterator339136->second;

            _count339051 = (_count339051 - 1);
          } else {
            _var339046.push_back(_var339047);
          }
        }
        std::vector< LINEITEM  > __var258400339053 = std::move(_var339046);
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > _map339054 = (std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > ());
        for (LINEITEM _l339056 : __var258400339053) {
          {
            int _var70841 = (_l339056.orderkey);
            std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator339137 = _map339054.find(_var70841);
            if ((_map_iterator339137 == _map339054.end())) {
              _map_iterator339137 = (_map339054.emplace(_var70841, (std::vector< LINEITEM  > ())).first);
            }
            std::vector< LINEITEM  > &_v339055 = _map_iterator339137->second;

            std::vector< LINEITEM  > _var339057 = (std::vector< LINEITEM  > ());
            for (LINEITEM _l339059 : __var258400339053) {
              if ((((_l339059.orderkey) == _var70841))) {
                {
                  _var339057.push_back(_l339059);
                }
              }
            }
            _v339055 = std::move(_var339057);
          }
        }
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::const_iterator _map_iterator339138 = (std::move(_map339054).find(__var242931339037));
        std::vector< LINEITEM  > _v339139;
        if ((_map_iterator339138 == std::move(_map339054).end())) {
          _v339139 = (std::vector< LINEITEM  > ());
        } else {
          _v339139 = (_map_iterator339138->second);
        }
        _conditional_result339038 = ((std::move(_var339043) == _v339139));
      } else {
        std::vector< LINEITEM  > _var339060 = (std::vector< LINEITEM  > ());
        std::unordered_map< LINEITEM , int , _HashLINEITEM > _histogram339062 = (std::unordered_map< LINEITEM , int , _HashLINEITEM > ());
        for (LINEITEM _l339066 : _var8585) {
          if ((((_l339066.orderkey) == orderkey))) {
            {
              std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator339140 = _histogram339062.find(_l339066);
              if ((_map_iterator339140 == _histogram339062.end())) {
                _map_iterator339140 = (_histogram339062.emplace(_l339066, 0).first);
              }
              int &_count339064 = _map_iterator339140->second;

              _count339064 = (_count339064 + 1);
            }
          }
        }
        for (LINEITEM _var339061 : _var8585) {
          std::unordered_map< LINEITEM , int , _HashLINEITEM >::const_iterator _map_iterator339141 = (_histogram339062.find(_var339061));
          int _v339142;
          if ((_map_iterator339141 == _histogram339062.end())) {
            _v339142 = 0;
          } else {
            _v339142 = (_map_iterator339141->second);
          }
          if ((_v339142 > 0)) {
            std::unordered_map< LINEITEM , int , _HashLINEITEM >::iterator _map_iterator339143 = _histogram339062.find(_var339061);
            if ((_map_iterator339143 == _histogram339062.end())) {
              _map_iterator339143 = (_histogram339062.emplace(_var339061, 0).first);
            }
            int &_count339065 = _map_iterator339143->second;

            _count339065 = (_count339065 - 1);
          } else {
            _var339060.push_back(_var339061);
          }
        }
        std::vector< LINEITEM  > __var258400339067 = std::move(_var339060);
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > _map339068 = (std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > > ());
        for (LINEITEM _l339070 : __var258400339067) {
          {
            int _var70841 = (_l339070.orderkey);
            std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator339144 = _map339068.find(_var70841);
            if ((_map_iterator339144 == _map339068.end())) {
              _map_iterator339144 = (_map339068.emplace(_var70841, (std::vector< LINEITEM  > ())).first);
            }
            std::vector< LINEITEM  > &_v339069 = _map_iterator339144->second;

            std::vector< LINEITEM  > _var339071 = (std::vector< LINEITEM  > ());
            for (LINEITEM _l339073 : __var258400339067) {
              if ((((_l339073.orderkey) == _var70841))) {
                {
                  _var339071.push_back(_l339073);
                }
              }
            }
            _v339069 = std::move(_var339071);
          }
        }
        std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::const_iterator _map_iterator339145 = (std::move(_map339068).find(__var242931339037));
        std::vector< LINEITEM  > _v339146;
        if ((_map_iterator339145 == std::move(_map339068).end())) {
          _v339146 = (std::vector< LINEITEM  > ());
        } else {
          _v339146 = (_map_iterator339145->second);
        }
        _conditional_result339038 = (((std::vector< LINEITEM  > ()) == _v339146));
      }
      bool _v339147;
      if ((!(_var74137.find(__var242931339037) != _var74137.end()))) {
        _v339147 = true;
      } else {
        _v339147 = (!(_conditional_result339038));
      }
      if (_v339147) {
        {
          _var339035.push_back(__var242931339037);
        }
      }
    }
    std::vector< int  > _var338667 = std::move(_var339035);
    std::unordered_map< _Type338676 , int , _Hash_Type338676 > _histogram339088 = (std::unordered_map< _Type338676 , int , _Hash_Type338676 > ());
    for (LINEITEM __var22124339093 : _var207705) {
      if ((!((((__var22124339093.orderkey) == orderkey))))) {
        {
          {
            std::unordered_map< _Type338676 , int , _Hash_Type338676 >::iterator _map_iterator339148 = _histogram339088.find((_Type338676((__var22124339093.returnflag), (__var22124339093.linestatus))));
            if ((_map_iterator339148 == _histogram339088.end())) {
              _map_iterator339148 = (_histogram339088.emplace((_Type338676((__var22124339093.returnflag), (__var22124339093.linestatus))), 0).first);
            }
            int &_count339090 = _map_iterator339148->second;

            _count339090 = (_count339090 + 1);
          }
        }
      }
    }
    for (_Type338676 _var287669 : _var16312) {
      std::unordered_map< _Type338676 , int , _Hash_Type338676 >::const_iterator _map_iterator339149 = (_histogram339088.find(_var287669));
      int _v339150;
      if ((_map_iterator339149 == _histogram339088.end())) {
        _v339150 = 0;
      } else {
        _v339150 = (_map_iterator339149->second);
      }
      if ((_v339150 > 0)) {
        std::unordered_map< _Type338676 , int , _Hash_Type338676 >::iterator _map_iterator339151 = _histogram339088.find(_var287669);
        if ((_map_iterator339151 == _histogram339088.end())) {
          _map_iterator339151 = (_histogram339088.emplace(_var287669, 0).first);
        }
        int &_count339091 = _map_iterator339151->second;

        _count339091 = (_count339091 - 1);
      } else {
        _var252302.erase(_var287669);
      }
    }
    for (_Type338676 _var134332 : _var338663) {
      auto _it339152(::std::find(_var99701.begin(), _var99701.end(), _var134332));
      if (_it339152 != _var99701.end()) { _var99701.erase(_it339152); }
    }
    for (_Type338676 _var26208 : _var338664) {
      auto _it339153(::std::find(_var16312.begin(), _var16312.end(), _var26208));
      if (_it339153 != _var16312.end()) { _var16312.erase(_it339153); }
    }
    for (LINEITEM _var315974 : _var338665) {
      auto _it339154(::std::find(_var207705.begin(), _var207705.end(), _var315974));
      if (_it339154 != _var207705.end()) { _var207705.erase(_it339154); }
    }
    std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::const_iterator _map_iterator339155 = (_var74137.find(orderkey));
    std::vector< LINEITEM  > _v339156;
    if ((_map_iterator339155 == _var74137.end())) {
      _v339156 = (std::vector< LINEITEM  > ());
    } else {
      _v339156 = (_map_iterator339155->second);
    }
    for (LINEITEM _var49504 : _v339156) {
      auto _it339157(::std::find(_var8585.begin(), _var8585.end(), _var49504));
      if (_it339157 != _var8585.end()) { _var8585.erase(_it339157); }
    }
    for (int _var242931 : _var338666) {
      _var74137.erase(_var242931);
    }
    for (int _var242931 : _var338667) {
      std::unordered_map< int , std::vector< LINEITEM  > , std::hash<int > >::iterator _map_iterator339158 = _var74137.find(_var242931);
      if ((_map_iterator339158 == _var74137.end())) {
        _map_iterator339158 = (_var74137.emplace(_var242931, (std::vector< LINEITEM  > ())).first);
      }
      std::vector< LINEITEM  > &_var242933 = _map_iterator339158->second;

    }
  }
};
