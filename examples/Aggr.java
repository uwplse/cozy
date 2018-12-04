public class Aggr implements java.io.Serializable {
  protected java.util.ArrayList<Integer > _var33;
  public Aggr() {
    clear();
  }

  public Aggr(java.util.ArrayList<Integer > l) {
    _var33 = l;
  }
  public void clear() {
    _var33 = new java.util.ArrayList<Integer > ();
  }
  public void elems(java.util.function.Consumer<Integer > _callback) {
    for (Integer _x92 : _var33) {
      _callback.accept(_x92);
    }
  }
  public Integer totalSum() {
    Integer _sum93 = 0;
    for (Integer _i95 : _var33) {
      {
        _sum93 = (_sum93 + _i95);
      }
    }
    return _sum93;
  }
  public Integer countGt10() {
    Integer _sum96 = 0;
    for (Integer _x99 : _var33) {
      if ((_x99 > 10)) {
        {
          {
            _sum96 = (_sum96 + 1);
          }
        }
      }
    }
    return _sum96;
  }
  public void add(Integer i) {
    java.util.ArrayList<Integer > _var100 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram102 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x103 : _var33) {
      Integer _count104 = _histogram102.getOrDefault(_x103, 0);
      _count104 = (_count104 + 1);
      _histogram102.put(_x103, _count104);

    }
    {
      Integer _count104 = _histogram102.getOrDefault(i, 0);
      _count104 = (_count104 + 1);
      _histogram102.put(i, _count104);

    }
    for (Integer _var101 : _var33) {
      if ((_histogram102.getOrDefault(_var101, 0) > 0)) {
        Integer _count105 = _histogram102.getOrDefault(_var101, 0);
        _count105 = (_count105 - 1);
        _histogram102.put(_var101, _count105);

      } else {
        _var100.add(_var101);
      }
    }
    java.util.ArrayList<Integer > _var90 = _var100;
    java.util.ArrayList<Integer > _var106 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram108 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x109 : _var33) {
      Integer _count110 = _histogram108.getOrDefault(_x109, 0);
      _count110 = (_count110 + 1);
      _histogram108.put(_x109, _count110);

    }
    for (Integer _var107 : _var33) {
      if ((_histogram108.getOrDefault(_var107, 0) > 0)) {
        Integer _count111 = _histogram108.getOrDefault(_var107, 0);
        _count111 = (_count111 - 1);
        _histogram108.put(_var107, _count111);

      } else {
        _var106.add(_var107);
      }
    }
    {
      if ((_histogram108.getOrDefault(i, 0) > 0)) {
        Integer _count111 = _histogram108.getOrDefault(i, 0);
        _count111 = (_count111 - 1);
        _histogram108.put(i, _count111);

      } else {
        _var106.add(i);
      }
    }
    java.util.ArrayList<Integer > _var91 = _var106;
    for (Integer _var50 : _var90) {
      _var33.remove(_var50);
    }
    for (Integer _var50 : _var91) {
      _var33.add(_var50);
    }
  }
}

