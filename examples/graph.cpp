#pragma once
#include <algorithm>
#include <functional>
#include <vector>
#include <unordered_set>
#include <string>
#include <unordered_map>

class Graph {
public:
  struct _Type1404 {
    int id;
    inline _Type1404() { }
    inline _Type1404(int _id) : id(::std::move(_id)) { }
    inline bool operator==(const _Type1404& other) const {
      return ((((*this).id) == (other.id)));
    }
  };
  struct _Hash_Type1404 {
    typedef Graph::_Type1404 argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code1408 = 0;
      int _hash_code1409 = 0;
      _hash_code1409 = (std::hash<int >()((x.id)));
      _hash_code1408 = ((_hash_code1408 * 31) ^ (_hash_code1409));
      return _hash_code1408;
    }
  };
  struct Node {
  public:
    _Type1404 val;
  private:
  };
    struct _Type1406 {
    int src;
    int dst;
    inline _Type1406() { }
    inline _Type1406(int _src, int _dst) : src(::std::move(_src)), dst(::std::move(_dst)) { }
    inline bool operator==(const _Type1406& other) const {
      bool _v1410;
      if (((((*this).src) == (other.src)))) {
        _v1410 = ((((*this).dst) == (other.dst)));
      } else {
        _v1410 = false;
      }
      return _v1410;
    }
  };
  struct _Hash_Type1406 {
    typedef Graph::_Type1406 argument_type;
    typedef std::size_t result_type;
    result_type operator()(const argument_type& x) const noexcept {
      int _hash_code1411 = 0;
      int _hash_code1412 = 0;
      _hash_code1412 = (std::hash<int >()((x.src)));
      _hash_code1411 = ((_hash_code1411 * 31) ^ (_hash_code1412));
      _hash_code1412 = (std::hash<int >()((x.dst)));
      _hash_code1411 = ((_hash_code1411 * 31) ^ (_hash_code1412));
      return _hash_code1411;
    }
  };
  struct Edge {
  public:
    _Type1406 val;
  private:
  };
  protected:
  std::vector< Edge * > _var268;
public:
  inline Graph() {
    _var268 = (std::vector< Edge * > ());
  }
  explicit inline Graph(std::vector< Node * > nodes, std::vector< Edge * > edges) {
    _var268 = edges;
  }
  Graph(const Graph& other) = delete;
  inline int  out_degree(int nodeId) {
    int _sum1413 = 0;
    for (Edge *_e1416 : _var268) {
      _Type1406 _v1417;
      if (((_e1416 == nullptr))) {
        _v1417 = (_Type1406 (0, 0));
      } else {
        _v1417 = (_e1416->val);
      }
      if ((((_v1417.src) == nodeId))) {
        {
          {
            _sum1413 = (_sum1413 + 1);
          }
        }
      }
    }
    return _sum1413;
  }
  inline void addNode (Node *n) {
  }
  inline void addEdge (Edge *e) {
    std::vector< Edge * > _var1418 = (std::vector< Edge * > ());
    std::unordered_map< Edge *, int , std::hash<Edge *> > _histogram1420 = (std::unordered_map< Edge *, int , std::hash<Edge *> > ());
    for (Edge *_x1421 : _var268) {
      std::unordered_map< Edge *, int , std::hash<Edge *> >::iterator _map_iterator1430 = _histogram1420.find(_x1421);
      if ((_map_iterator1430 == _histogram1420.end())) {
        _map_iterator1430 = (_histogram1420.emplace(_x1421, 0).first);
      }
      int &_count1422 = _map_iterator1430->second;

      _count1422 = (_count1422 + 1);
    }
    {
      std::unordered_map< Edge *, int , std::hash<Edge *> >::iterator _map_iterator1431 = _histogram1420.find(e);
      if ((_map_iterator1431 == _histogram1420.end())) {
        _map_iterator1431 = (_histogram1420.emplace(e, 0).first);
      }
      int &_count1422 = _map_iterator1431->second;

      _count1422 = (_count1422 + 1);
    }
    for (Edge *_var1419 : _var268) {
      std::unordered_map< Edge *, int , std::hash<Edge *> >::const_iterator _map_iterator1432 = (_histogram1420.find(_var1419));
      int _v1433;
      if ((_map_iterator1432 == _histogram1420.end())) {
        _v1433 = 0;
      } else {
        _v1433 = (_map_iterator1432->second);
      }
      if ((_v1433 > 0)) {
        std::unordered_map< Edge *, int , std::hash<Edge *> >::iterator _map_iterator1434 = _histogram1420.find(_var1419);
        if ((_map_iterator1434 == _histogram1420.end())) {
          _map_iterator1434 = (_histogram1420.emplace(_var1419, 0).first);
        }
        int &_count1423 = _map_iterator1434->second;

        _count1423 = (_count1423 - 1);
      } else {
        _var1418.push_back(_var1419);
      }
    }
    std::vector< Edge * > _var1376 = std::move(_var1418);
    std::vector< Edge * > _var1424 = (std::vector< Edge * > ());
    std::unordered_map< Edge *, int , std::hash<Edge *> > _histogram1426 = (std::unordered_map< Edge *, int , std::hash<Edge *> > ());
    for (Edge *_x1427 : _var268) {
      std::unordered_map< Edge *, int , std::hash<Edge *> >::iterator _map_iterator1435 = _histogram1426.find(_x1427);
      if ((_map_iterator1435 == _histogram1426.end())) {
        _map_iterator1435 = (_histogram1426.emplace(_x1427, 0).first);
      }
      int &_count1428 = _map_iterator1435->second;

      _count1428 = (_count1428 + 1);
    }
    for (Edge *_var1425 : _var268) {
      std::unordered_map< Edge *, int , std::hash<Edge *> >::const_iterator _map_iterator1436 = (_histogram1426.find(_var1425));
      int _v1437;
      if ((_map_iterator1436 == _histogram1426.end())) {
        _v1437 = 0;
      } else {
        _v1437 = (_map_iterator1436->second);
      }
      if ((_v1437 > 0)) {
        std::unordered_map< Edge *, int , std::hash<Edge *> >::iterator _map_iterator1438 = _histogram1426.find(_var1425);
        if ((_map_iterator1438 == _histogram1426.end())) {
          _map_iterator1438 = (_histogram1426.emplace(_var1425, 0).first);
        }
        int &_count1429 = _map_iterator1438->second;

        _count1429 = (_count1429 - 1);
      } else {
        _var1424.push_back(_var1425);
      }
    }
    {
      std::unordered_map< Edge *, int , std::hash<Edge *> >::const_iterator _map_iterator1439 = (_histogram1426.find(e));
      int _v1440;
      if ((_map_iterator1439 == _histogram1426.end())) {
        _v1440 = 0;
      } else {
        _v1440 = (_map_iterator1439->second);
      }
      if ((_v1440 > 0)) {
        std::unordered_map< Edge *, int , std::hash<Edge *> >::iterator _map_iterator1441 = _histogram1426.find(e);
        if ((_map_iterator1441 == _histogram1426.end())) {
          _map_iterator1441 = (_histogram1426.emplace(e, 0).first);
        }
        int &_count1429 = _map_iterator1441->second;

        _count1429 = (_count1429 - 1);
      } else {
        _var1424.push_back(e);
      }
    }
    std::vector< Edge * > _var1377 = std::move(_var1424);
    for (Edge *_var458 : _var1376) {
      auto _it1442(::std::find(_var268.begin(), _var268.end(), _var458));
      if (_it1442 != _var268.end()) { _var268.erase(_it1442); }
    }
    for (Edge *_var458 : _var1377) {
      _var268.push_back(_var458);
    }
  }
};
