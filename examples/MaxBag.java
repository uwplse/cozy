public class MaxBag implements java.io.Serializable {
  protected java.util.ArrayList<Integer > _var73;
  public MaxBag() {
    clear();
  }

  public MaxBag(java.util.ArrayList<Integer > l) {
    _var73 = l;
  }
  public void clear() {
    _var73 = new java.util.ArrayList<Integer > ();
  }
  public Integer get_max() {
    Integer _max197 = 0;
    Boolean _first198 = true;
    for (Integer _x199 : _var73) {
      Boolean _v200;
      if (_first198) {
        _v200 = true;
      } else {
        _v200 = (_x199 > _max197);
      }
      if (_v200) {
        _first198 = false;
        _max197 = _x199;
      }
    }
    return _max197;
  }
  public void add(Integer x) {
    java.util.ArrayList<Integer > _var201 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram203 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x204 : _var73) {
      Integer _count205 = _histogram203.getOrDefault(_x204, 0);
      _count205 = (_count205 + 1);
      _histogram203.put(_x204, _count205);

    }
    {
      Integer _count205 = _histogram203.getOrDefault(x, 0);
      _count205 = (_count205 + 1);
      _histogram203.put(x, _count205);

    }
    for (Integer _var202 : _var73) {
      if ((_histogram203.getOrDefault(_var202, 0) > 0)) {
        Integer _count206 = _histogram203.getOrDefault(_var202, 0);
        _count206 = (_count206 - 1);
        _histogram203.put(_var202, _count206);

      } else {
        _var201.add(_var202);
      }
    }
    java.util.ArrayList<Integer > _var193 = _var201;
    java.util.ArrayList<Integer > _var207 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram209 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x210 : _var73) {
      Integer _count211 = _histogram209.getOrDefault(_x210, 0);
      _count211 = (_count211 + 1);
      _histogram209.put(_x210, _count211);

    }
    for (Integer _var208 : _var73) {
      if ((_histogram209.getOrDefault(_var208, 0) > 0)) {
        Integer _count212 = _histogram209.getOrDefault(_var208, 0);
        _count212 = (_count212 - 1);
        _histogram209.put(_var208, _count212);

      } else {
        _var207.add(_var208);
      }
    }
    {
      if ((_histogram209.getOrDefault(x, 0) > 0)) {
        Integer _count212 = _histogram209.getOrDefault(x, 0);
        _count212 = (_count212 - 1);
        _histogram209.put(x, _count212);

      } else {
        _var207.add(x);
      }
    }
    java.util.ArrayList<Integer > _var194 = _var207;
    for (Integer _var94 : _var193) {
      _var73.remove(_var94);
    }
    for (Integer _var94 : _var194) {
      _var73.add(_var94);
    }
  }
  public void remove(Integer x) {
    java.util.ArrayList<Integer > _var213 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram215 = new java.util.HashMap<Integer , Integer > ();
    java.util.HashMap<Integer , Integer > _histogram219 = new java.util.HashMap<Integer , Integer > ();
    {
      Integer _count221 = _histogram219.getOrDefault(x, 0);
      _count221 = (_count221 + 1);
      _histogram219.put(x, _count221);

    }
    for (Integer _x216 : _var73) {
      if ((_histogram219.getOrDefault(_x216, 0) > 0)) {
        Integer _count222 = _histogram219.getOrDefault(_x216, 0);
        _count222 = (_count222 - 1);
        _histogram219.put(_x216, _count222);

      } else {
        Integer _count217 = _histogram215.getOrDefault(_x216, 0);
        _count217 = (_count217 + 1);
        _histogram215.put(_x216, _count217);

      }
    }
    for (Integer _var214 : _var73) {
      if ((_histogram215.getOrDefault(_var214, 0) > 0)) {
        Integer _count218 = _histogram215.getOrDefault(_var214, 0);
        _count218 = (_count218 - 1);
        _histogram215.put(_var214, _count218);

      } else {
        _var213.add(_var214);
      }
    }
    java.util.ArrayList<Integer > _var195 = _var213;
    java.util.ArrayList<Integer > _var223 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram225 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x226 : _var73) {
      Integer _count227 = _histogram225.getOrDefault(_x226, 0);
      _count227 = (_count227 + 1);
      _histogram225.put(_x226, _count227);

    }
    java.util.HashMap<Integer , Integer > _histogram229 = new java.util.HashMap<Integer , Integer > ();
    {
      Integer _count231 = _histogram229.getOrDefault(x, 0);
      _count231 = (_count231 + 1);
      _histogram229.put(x, _count231);

    }
    for (Integer _var224 : _var73) {
      if ((_histogram229.getOrDefault(_var224, 0) > 0)) {
        Integer _count232 = _histogram229.getOrDefault(_var224, 0);
        _count232 = (_count232 - 1);
        _histogram229.put(_var224, _count232);

      } else {
        if ((_histogram225.getOrDefault(_var224, 0) > 0)) {
          Integer _count228 = _histogram225.getOrDefault(_var224, 0);
          _count228 = (_count228 - 1);
          _histogram225.put(_var224, _count228);

        } else {
          _var223.add(_var224);
        }
      }
    }
    java.util.ArrayList<Integer > _var196 = _var223;
    for (Integer _var171 : _var195) {
      _var73.remove(_var171);
    }
    for (Integer _var171 : _var196) {
      _var73.add(_var171);
    }
  }
}

