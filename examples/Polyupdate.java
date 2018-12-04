public class Polyupdate implements java.io.Serializable {
  protected Integer _var23;
  protected java.util.ArrayList<Integer > _var24;
  public Polyupdate() {
    clear();
  }

  public Polyupdate(java.util.ArrayList<Integer > x, Integer s) {
    _var23 = s;
    _var24 = x;
  }
  public void clear() {
    _var23 = 0;
    _var24 = new java.util.ArrayList<Integer > ();
  }
  public Integer sm() {
    Integer _sum94 = 0;
    for (Integer _x95 : _var24) {
      _sum94 = (_sum94 + _x95);
    }
    return (_var23 + _sum94);
  }
  public void a(Integer y) {
    Integer _conditional_result96 = 0;
    if ((y > 0)) {
      _conditional_result96 = (_var23 + y);
    } else {
      _conditional_result96 = _var23;
    }
    Integer _var91 = _conditional_result96;
    java.util.ArrayList<Integer > _var97 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram99 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x100 : _var24) {
      Integer _count101 = _histogram99.getOrDefault(_x100, 0);
      _count101 = (_count101 + 1);
      _histogram99.put(_x100, _count101);

    }
    {
      Integer _count101 = _histogram99.getOrDefault(y, 0);
      _count101 = (_count101 + 1);
      _histogram99.put(y, _count101);

    }
    for (Integer _var98 : _var24) {
      if ((_histogram99.getOrDefault(_var98, 0) > 0)) {
        Integer _count102 = _histogram99.getOrDefault(_var98, 0);
        _count102 = (_count102 - 1);
        _histogram99.put(_var98, _count102);

      } else {
        _var97.add(_var98);
      }
    }
    java.util.ArrayList<Integer > _var92 = _var97;
    java.util.ArrayList<Integer > _var103 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram105 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x106 : _var24) {
      Integer _count107 = _histogram105.getOrDefault(_x106, 0);
      _count107 = (_count107 + 1);
      _histogram105.put(_x106, _count107);

    }
    for (Integer _var104 : _var24) {
      if ((_histogram105.getOrDefault(_var104, 0) > 0)) {
        Integer _count108 = _histogram105.getOrDefault(_var104, 0);
        _count108 = (_count108 - 1);
        _histogram105.put(_var104, _count108);

      } else {
        _var103.add(_var104);
      }
    }
    {
      if ((_histogram105.getOrDefault(y, 0) > 0)) {
        Integer _count108 = _histogram105.getOrDefault(y, 0);
        _count108 = (_count108 - 1);
        _histogram105.put(y, _count108);

      } else {
        _var103.add(y);
      }
    }
    java.util.ArrayList<Integer > _var93 = _var103;
    _var23 = _var91;
    for (Integer _var56 : _var92) {
      _var24.remove(_var56);
    }
    for (Integer _var56 : _var93) {
      _var24.add(_var56);
    }
  }
}

