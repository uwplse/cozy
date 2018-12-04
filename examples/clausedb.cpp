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
  std::vector< std::unordered_set< int , std::hash<int > >  > _var460;
  std::vector< int  > _var461;
public:
  inline ClauseDB() {
    _var460 = (std::vector< std::unordered_set< int , std::hash<int > >  > ());
    _var461 = (std::vector< int  > ());
  }
  explicit inline ClauseDB(int N, std::vector< std::unordered_set< int , std::hash<int > >  > clauses, std::vector< int  > falselits) {
    _var460 = clauses;
    _var461 = falselits;
  }
  ClauseDB(const ClauseDB& other) = delete;
  inline bool  unsat() {
    bool _v1316 = true;
    {
      for (std::unordered_set< int , std::hash<int > > _c1320 : _var460) {
        bool _v1321 = true;
        {
          for (int _l1325 : _c1320) {
            bool _found1326 = false;
            {
              for (int _x1327 : _var461) {
                if (((_x1327 == _l1325))) {
                  _found1326 = true;
                  goto _label1331;
                }
              }
            }
_label1331:
            if ((!(_found1326))) {
              {
                {
                  _v1321 = false;
                  goto _label1330;
                }
              }
            }
          }
        }
_label1330:
        if (_v1321) {
          {
            {
              _v1316 = false;
              goto _label1329;
            }
          }
        }
      }
    }
_label1329:
    return (!(_v1316));
  }
  template <class F>
  inline void unit(const F& _callback) {
    for (std::unordered_set< int , std::hash<int > > _c1334 : _var460) {
      int _sum1335 = 0;
      for (int _l1338 : _c1334) {
        bool _found1339 = false;
        {
          for (int _x1340 : _var461) {
            if (((_x1340 == _l1338))) {
              _found1339 = true;
              goto _label1342;
            }
          }
        }
_label1342:
        if ((!(_found1339))) {
          {
            {
              _sum1335 = (_sum1335 + 1);
            }
          }
        }
      }
      if (((_sum1335 == 1))) {
        {
          {
            _callback(_c1334);
          }
        }
      }
    }
  }
  inline void addClause (std::unordered_set< int , std::hash<int > > c) {
    std::vector< std::unordered_set< int , std::hash<int > >  > _var1343 = (std::vector< std::unordered_set< int , std::hash<int > >  > ());
    std::vector< std::unordered_set< int , std::hash<int > >  > _var1346 = (std::vector< std::unordered_set< int , std::hash<int > >  > ());
    for (std::unordered_set< int , std::hash<int > > _var1347 : _var460) {
      _var1346.push_back(_var1347);
    }
    {
      _var1346.push_back(c);
    }
    std::vector< std::unordered_set< int , std::hash<int > >  > _bag_subtraction_right1345 = std::move(_var1346);
    for (std::unordered_set< int , std::hash<int > > _var1344 : _var460) {
      bool _found1348 = false;
      {
        for (std::unordered_set< int , std::hash<int > > _x1349 : _bag_subtraction_right1345) {
          if (((_x1349 == _var1344))) {
            _found1348 = true;
            goto _label1360;
          }
        }
      }
_label1360:
      if (_found1348) {
        auto _it1361(::std::find(_bag_subtraction_right1345.begin(), _bag_subtraction_right1345.end(), _var1344));
        if (_it1361 != _bag_subtraction_right1345.end()) { _bag_subtraction_right1345.erase(_it1361); }
      } else {
        _var1343.push_back(_var1344);
      }
    }
    std::vector< std::unordered_set< int , std::hash<int > >  > _var1238 = std::move(_var1343);
    std::vector< std::unordered_set< int , std::hash<int > >  > _var1351 = (std::vector< std::unordered_set< int , std::hash<int > >  > ());
    std::vector< std::unordered_set< int , std::hash<int > >  > _bag_subtraction_right1353 = _var460;
    for (std::unordered_set< int , std::hash<int > > _var1352 : _var460) {
      bool _found1354 = false;
      {
        for (std::unordered_set< int , std::hash<int > > _x1355 : _bag_subtraction_right1353) {
          if (((_x1355 == _var1352))) {
            _found1354 = true;
            goto _label1362;
          }
        }
      }
_label1362:
      if (_found1354) {
        auto _it1363(::std::find(_bag_subtraction_right1353.begin(), _bag_subtraction_right1353.end(), _var1352));
        if (_it1363 != _bag_subtraction_right1353.end()) { _bag_subtraction_right1353.erase(_it1363); }
      } else {
        _var1351.push_back(_var1352);
      }
    }
    {
      bool _found1357 = false;
      {
        for (std::unordered_set< int , std::hash<int > > _x1358 : _bag_subtraction_right1353) {
          if (((_x1358 == c))) {
            _found1357 = true;
            goto _label1364;
          }
        }
      }
_label1364:
      if (_found1357) {
        auto _it1365(::std::find(_bag_subtraction_right1353.begin(), _bag_subtraction_right1353.end(), c));
        if (_it1365 != _bag_subtraction_right1353.end()) { _bag_subtraction_right1353.erase(_it1365); }
      } else {
        _var1351.push_back(c);
      }
    }
    std::vector< std::unordered_set< int , std::hash<int > >  > _var1239 = std::move(_var1351);
    for (std::unordered_set< int , std::hash<int > > _var535 : _var1238) {
      auto _it1366(::std::find(_var460.begin(), _var460.end(), _var535));
      if (_it1366 != _var460.end()) { _var460.erase(_it1366); }
    }
    for (std::unordered_set< int , std::hash<int > > _var535 : _var1239) {
      _var460.push_back(_var535);
    }
  }
  inline void falsify (int l) {
    std::vector< int  > _var1367 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram1369 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x1370 : _var461) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator1379 = _histogram1369.find(_x1370);
      if ((_map_iterator1379 == _histogram1369.end())) {
        _map_iterator1379 = (_histogram1369.emplace(_x1370, 0).first);
      }
      int &_count1371 = _map_iterator1379->second;

      _count1371 = (_count1371 + 1);
    }
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator1380 = _histogram1369.find(l);
      if ((_map_iterator1380 == _histogram1369.end())) {
        _map_iterator1380 = (_histogram1369.emplace(l, 0).first);
      }
      int &_count1371 = _map_iterator1380->second;

      _count1371 = (_count1371 + 1);
    }
    for (int _var1368 : _var461) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator1381 = (_histogram1369.find(_var1368));
      int _v1382;
      if ((_map_iterator1381 == _histogram1369.end())) {
        _v1382 = 0;
      } else {
        _v1382 = (_map_iterator1381->second);
      }
      if ((_v1382 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator1383 = _histogram1369.find(_var1368);
        if ((_map_iterator1383 == _histogram1369.end())) {
          _map_iterator1383 = (_histogram1369.emplace(_var1368, 0).first);
        }
        int &_count1372 = _map_iterator1383->second;

        _count1372 = (_count1372 - 1);
      } else {
        _var1367.push_back(_var1368);
      }
    }
    std::vector< int  > _var1240 = std::move(_var1367);
    std::vector< int  > _var1373 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram1375 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x1376 : _var461) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator1384 = _histogram1375.find(_x1376);
      if ((_map_iterator1384 == _histogram1375.end())) {
        _map_iterator1384 = (_histogram1375.emplace(_x1376, 0).first);
      }
      int &_count1377 = _map_iterator1384->second;

      _count1377 = (_count1377 + 1);
    }
    for (int _var1374 : _var461) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator1385 = (_histogram1375.find(_var1374));
      int _v1386;
      if ((_map_iterator1385 == _histogram1375.end())) {
        _v1386 = 0;
      } else {
        _v1386 = (_map_iterator1385->second);
      }
      if ((_v1386 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator1387 = _histogram1375.find(_var1374);
        if ((_map_iterator1387 == _histogram1375.end())) {
          _map_iterator1387 = (_histogram1375.emplace(_var1374, 0).first);
        }
        int &_count1378 = _map_iterator1387->second;

        _count1378 = (_count1378 - 1);
      } else {
        _var1373.push_back(_var1374);
      }
    }
    {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator1388 = (_histogram1375.find(l));
      int _v1389;
      if ((_map_iterator1388 == _histogram1375.end())) {
        _v1389 = 0;
      } else {
        _v1389 = (_map_iterator1388->second);
      }
      if ((_v1389 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator1390 = _histogram1375.find(l);
        if ((_map_iterator1390 == _histogram1375.end())) {
          _map_iterator1390 = (_histogram1375.emplace(l, 0).first);
        }
        int &_count1378 = _map_iterator1390->second;

        _count1378 = (_count1378 - 1);
      } else {
        _var1373.push_back(l);
      }
    }
    std::vector< int  > _var1241 = std::move(_var1373);
    for (int _var925 : _var1240) {
      auto _it1391(::std::find(_var461.begin(), _var461.end(), _var925));
      if (_it1391 != _var461.end()) { _var461.erase(_it1391); }
    }
    for (int _var925 : _var1241) {
      _var461.push_back(_var925);
    }
  }
  inline void unfalsify (int l) {
    std::vector< int  > _var1392 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram1394 = (std::unordered_map< int , int , std::hash<int > > ());
    std::unordered_map< int , int , std::hash<int > > _histogram1398 = (std::unordered_map< int , int , std::hash<int > > ());
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator1412 = _histogram1398.find(l);
      if ((_map_iterator1412 == _histogram1398.end())) {
        _map_iterator1412 = (_histogram1398.emplace(l, 0).first);
      }
      int &_count1400 = _map_iterator1412->second;

      _count1400 = (_count1400 + 1);
    }
    for (int _x1395 : _var461) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator1413 = (_histogram1398.find(_x1395));
      int _v1414;
      if ((_map_iterator1413 == _histogram1398.end())) {
        _v1414 = 0;
      } else {
        _v1414 = (_map_iterator1413->second);
      }
      if ((_v1414 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator1415 = _histogram1398.find(_x1395);
        if ((_map_iterator1415 == _histogram1398.end())) {
          _map_iterator1415 = (_histogram1398.emplace(_x1395, 0).first);
        }
        int &_count1401 = _map_iterator1415->second;

        _count1401 = (_count1401 - 1);
      } else {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator1416 = _histogram1394.find(_x1395);
        if ((_map_iterator1416 == _histogram1394.end())) {
          _map_iterator1416 = (_histogram1394.emplace(_x1395, 0).first);
        }
        int &_count1396 = _map_iterator1416->second;

        _count1396 = (_count1396 + 1);
      }
    }
    for (int _var1393 : _var461) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator1417 = (_histogram1394.find(_var1393));
      int _v1418;
      if ((_map_iterator1417 == _histogram1394.end())) {
        _v1418 = 0;
      } else {
        _v1418 = (_map_iterator1417->second);
      }
      if ((_v1418 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator1419 = _histogram1394.find(_var1393);
        if ((_map_iterator1419 == _histogram1394.end())) {
          _map_iterator1419 = (_histogram1394.emplace(_var1393, 0).first);
        }
        int &_count1397 = _map_iterator1419->second;

        _count1397 = (_count1397 - 1);
      } else {
        _var1392.push_back(_var1393);
      }
    }
    std::vector< int  > _var1242 = std::move(_var1392);
    std::vector< int  > _var1402 = (std::vector< int  > ());
    std::unordered_map< int , int , std::hash<int > > _histogram1404 = (std::unordered_map< int , int , std::hash<int > > ());
    for (int _x1405 : _var461) {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator1420 = _histogram1404.find(_x1405);
      if ((_map_iterator1420 == _histogram1404.end())) {
        _map_iterator1420 = (_histogram1404.emplace(_x1405, 0).first);
      }
      int &_count1406 = _map_iterator1420->second;

      _count1406 = (_count1406 + 1);
    }
    std::unordered_map< int , int , std::hash<int > > _histogram1408 = (std::unordered_map< int , int , std::hash<int > > ());
    {
      std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator1421 = _histogram1408.find(l);
      if ((_map_iterator1421 == _histogram1408.end())) {
        _map_iterator1421 = (_histogram1408.emplace(l, 0).first);
      }
      int &_count1410 = _map_iterator1421->second;

      _count1410 = (_count1410 + 1);
    }
    for (int _var1403 : _var461) {
      std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator1422 = (_histogram1408.find(_var1403));
      int _v1423;
      if ((_map_iterator1422 == _histogram1408.end())) {
        _v1423 = 0;
      } else {
        _v1423 = (_map_iterator1422->second);
      }
      if ((_v1423 > 0)) {
        std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator1424 = _histogram1408.find(_var1403);
        if ((_map_iterator1424 == _histogram1408.end())) {
          _map_iterator1424 = (_histogram1408.emplace(_var1403, 0).first);
        }
        int &_count1411 = _map_iterator1424->second;

        _count1411 = (_count1411 - 1);
      } else {
        std::unordered_map< int , int , std::hash<int > >::const_iterator _map_iterator1425 = (_histogram1404.find(_var1403));
        int _v1426;
        if ((_map_iterator1425 == _histogram1404.end())) {
          _v1426 = 0;
        } else {
          _v1426 = (_map_iterator1425->second);
        }
        if ((_v1426 > 0)) {
          std::unordered_map< int , int , std::hash<int > >::iterator _map_iterator1427 = _histogram1404.find(_var1403);
          if ((_map_iterator1427 == _histogram1404.end())) {
            _map_iterator1427 = (_histogram1404.emplace(_var1403, 0).first);
          }
          int &_count1407 = _map_iterator1427->second;

          _count1407 = (_count1407 - 1);
        } else {
          _var1402.push_back(_var1403);
        }
      }
    }
    std::vector< int  > _var1243 = std::move(_var1402);
    for (int _var1171 : _var1242) {
      auto _it1428(::std::find(_var461.begin(), _var461.end(), _var1171));
      if (_it1428 != _var461.end()) { _var461.erase(_it1428); }
    }
    for (int _var1171 : _var1243) {
      _var461.push_back(_var1171);
    }
  }
};
