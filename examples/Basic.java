public class Basic implements java.io.Serializable {
  protected java.util.ArrayList<Integer > _var23;
  public Basic() {
    clear();
  }

  public Basic(java.util.ArrayList<Integer > l) {
    _var23 = l;
  }
  public void clear() {
    _var23 = new java.util.ArrayList<Integer > ();
  }
  public void elems(java.util.function.Consumer<Integer > _callback) {
    for (Integer _x136 : _var23) {
      _callback.accept(_x136);
    }
  }
  public void add(Integer n) {
    java.util.ArrayList<Integer > _var137 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram139 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x140 : _var23) {
      Integer _count141 = _histogram139.getOrDefault(_x140, 0);
      _count141 = (_count141 + 1);
      _histogram139.put(_x140, _count141);

    }
    {
      Integer _count141 = _histogram139.getOrDefault(n, 0);
      _count141 = (_count141 + 1);
      _histogram139.put(n, _count141);

    }
    for (Integer _var138 : _var23) {
      if ((_histogram139.getOrDefault(_var138, 0) > 0)) {
        Integer _count142 = _histogram139.getOrDefault(_var138, 0);
        _count142 = (_count142 - 1);
        _histogram139.put(_var138, _count142);

      } else {
        _var137.add(_var138);
      }
    }
    java.util.ArrayList<Integer > _var132 = _var137;
    java.util.ArrayList<Integer > _var143 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram145 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x146 : _var23) {
      Integer _count147 = _histogram145.getOrDefault(_x146, 0);
      _count147 = (_count147 + 1);
      _histogram145.put(_x146, _count147);

    }
    for (Integer _var144 : _var23) {
      if ((_histogram145.getOrDefault(_var144, 0) > 0)) {
        Integer _count148 = _histogram145.getOrDefault(_var144, 0);
        _count148 = (_count148 - 1);
        _histogram145.put(_var144, _count148);

      } else {
        _var143.add(_var144);
      }
    }
    {
      if ((_histogram145.getOrDefault(n, 0) > 0)) {
        Integer _count148 = _histogram145.getOrDefault(n, 0);
        _count148 = (_count148 - 1);
        _histogram145.put(n, _count148);

      } else {
        _var143.add(n);
      }
    }
    java.util.ArrayList<Integer > _var133 = _var143;
    for (Integer _var40 : _var132) {
      _var23.remove(_var40);
    }
    for (Integer _var40 : _var133) {
      _var23.add(_var40);
    }
  }
  public void remove(Integer n) {
    java.util.ArrayList<Integer > _var149 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram151 = new java.util.HashMap<Integer , Integer > ();
    java.util.HashMap<Integer , Integer > _histogram155 = new java.util.HashMap<Integer , Integer > ();
    {
      Integer _count157 = _histogram155.getOrDefault(n, 0);
      _count157 = (_count157 + 1);
      _histogram155.put(n, _count157);

    }
    for (Integer _x152 : _var23) {
      if ((_histogram155.getOrDefault(_x152, 0) > 0)) {
        Integer _count158 = _histogram155.getOrDefault(_x152, 0);
        _count158 = (_count158 - 1);
        _histogram155.put(_x152, _count158);

      } else {
        Integer _count153 = _histogram151.getOrDefault(_x152, 0);
        _count153 = (_count153 + 1);
        _histogram151.put(_x152, _count153);

      }
    }
    for (Integer _var150 : _var23) {
      if ((_histogram151.getOrDefault(_var150, 0) > 0)) {
        Integer _count154 = _histogram151.getOrDefault(_var150, 0);
        _count154 = (_count154 - 1);
        _histogram151.put(_var150, _count154);

      } else {
        _var149.add(_var150);
      }
    }
    java.util.ArrayList<Integer > _var134 = _var149;
    java.util.ArrayList<Integer > _var159 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram161 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x162 : _var23) {
      Integer _count163 = _histogram161.getOrDefault(_x162, 0);
      _count163 = (_count163 + 1);
      _histogram161.put(_x162, _count163);

    }
    {
      Integer _count163 = _histogram161.getOrDefault(n, 0);
      _count163 = (_count163 + 1);
      _histogram161.put(n, _count163);

    }
    for (Integer _var160 : _var23) {
      if ((_histogram161.getOrDefault(_var160, 0) > 0)) {
        Integer _count164 = _histogram161.getOrDefault(_var160, 0);
        _count164 = (_count164 - 1);
        _histogram161.put(_var160, _count164);

      } else {
        _var159.add(_var160);
      }
    }
    java.util.ArrayList<Integer > _var135 = _var159;
    for (Integer _var89 : _var134) {
      _var23.remove(_var89);
    }
    for (Integer _var89 : _var135) {
      _var23.add(_var89);
    }
  }
}

