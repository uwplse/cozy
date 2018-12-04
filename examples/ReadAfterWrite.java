public class ReadAfterWrite implements java.io.Serializable {
  protected Integer _var24;
  protected java.util.ArrayList<Integer > _var38;
  public ReadAfterWrite() {
    clear();
  }

  public ReadAfterWrite(Integer x, java.util.ArrayList<Integer > l) {
    _var24 = x;
    _var38 = l;
  }
  public void clear() {
    _var24 = 0;
    _var38 = new java.util.ArrayList<Integer > ();
  }
  public Integer getx() {
    return _var24;
  }
  public void elems(java.util.function.Consumer<Integer > _callback) {
    for (Integer _x104 : _var38) {
      _callback.accept(_x104);
    }
  }
  public void do_thing(Integer n) {
    java.util.ArrayList<Integer > _var105 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram107 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x108 : _var38) {
      Integer _count109 = _histogram107.getOrDefault(_x108, 0);
      _count109 = (_count109 + 1);
      _histogram107.put(_x108, _count109);

    }
    {
      Integer _count109 = _histogram107.getOrDefault((_var24 + n), 0);
      _count109 = (_count109 + 1);
      _histogram107.put((_var24 + n), _count109);

    }
    for (Integer _var106 : _var38) {
      if ((_histogram107.getOrDefault(_var106, 0) > 0)) {
        Integer _count110 = _histogram107.getOrDefault(_var106, 0);
        _count110 = (_count110 - 1);
        _histogram107.put(_var106, _count110);

      } else {
        _var105.add(_var106);
      }
    }
    java.util.ArrayList<Integer > _var101 = _var105;
    java.util.ArrayList<Integer > _var111 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram113 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x114 : _var38) {
      Integer _count115 = _histogram113.getOrDefault(_x114, 0);
      _count115 = (_count115 + 1);
      _histogram113.put(_x114, _count115);

    }
    for (Integer _var112 : _var38) {
      if ((_histogram113.getOrDefault(_var112, 0) > 0)) {
        Integer _count116 = _histogram113.getOrDefault(_var112, 0);
        _count116 = (_count116 - 1);
        _histogram113.put(_var112, _count116);

      } else {
        _var111.add(_var112);
      }
    }
    {
      Integer _var112 = (_var24 + n);
      if ((_histogram113.getOrDefault(_var112, 0) > 0)) {
        Integer _count116 = _histogram113.getOrDefault(_var112, 0);
        _count116 = (_count116 - 1);
        _histogram113.put(_var112, _count116);

      } else {
        _var111.add(_var112);
      }
    }
    java.util.ArrayList<Integer > _var102 = _var111;
    Integer _var103 = (_var24 + n);
    for (Integer _var57 : _var101) {
      _var38.remove(_var57);
    }
    for (Integer _var57 : _var102) {
      _var38.add(_var57);
    }
    _var24 = _var103;
  }
}

