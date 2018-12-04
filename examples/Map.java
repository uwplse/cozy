public class Map implements java.io.Serializable {
  protected java.util.ArrayList<Integer > _var29;
  public Map() {
    clear();
  }

  public Map(java.util.ArrayList<Integer > xs) {
    _var29 = xs;
  }
  public void clear() {
    _var29 = new java.util.ArrayList<Integer > ();
  }
  public void a(Integer z, java.util.function.Consumer<Integer > _callback) {
    for (Integer _x151 : _var29) {
      if ((java.util.Objects.equals(_x151, z))) {
        {
          {
            _callback.accept(_x151);
          }
        }
      }
    }
  }
  public void add(Integer x) {
    java.util.ArrayList<Integer > _var152 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram154 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x155 : _var29) {
      Integer _count156 = _histogram154.getOrDefault(_x155, 0);
      _count156 = (_count156 + 1);
      _histogram154.put(_x155, _count156);

    }
    {
      Integer _count156 = _histogram154.getOrDefault(x, 0);
      _count156 = (_count156 + 1);
      _histogram154.put(x, _count156);

    }
    for (Integer _var153 : _var29) {
      if ((_histogram154.getOrDefault(_var153, 0) > 0)) {
        Integer _count157 = _histogram154.getOrDefault(_var153, 0);
        _count157 = (_count157 - 1);
        _histogram154.put(_var153, _count157);

      } else {
        _var152.add(_var153);
      }
    }
    java.util.ArrayList<Integer > _var145 = _var152;
    java.util.ArrayList<Integer > _var158 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram160 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x161 : _var29) {
      Integer _count162 = _histogram160.getOrDefault(_x161, 0);
      _count162 = (_count162 + 1);
      _histogram160.put(_x161, _count162);

    }
    for (Integer _var159 : _var29) {
      if ((_histogram160.getOrDefault(_var159, 0) > 0)) {
        Integer _count163 = _histogram160.getOrDefault(_var159, 0);
        _count163 = (_count163 - 1);
        _histogram160.put(_var159, _count163);

      } else {
        _var158.add(_var159);
      }
    }
    {
      if ((_histogram160.getOrDefault(x, 0) > 0)) {
        Integer _count163 = _histogram160.getOrDefault(x, 0);
        _count163 = (_count163 - 1);
        _histogram160.put(x, _count163);

      } else {
        _var158.add(x);
      }
    }
    java.util.ArrayList<Integer > _var146 = _var158;
    for (Integer _var46 : _var145) {
      _var29.remove(_var46);
    }
    for (Integer _var46 : _var146) {
      _var29.add(_var46);
    }
  }
  public void rm(Integer x) {
    java.util.ArrayList<Integer > _var164 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram166 = new java.util.HashMap<Integer , Integer > ();
    java.util.HashMap<Integer , Integer > _histogram170 = new java.util.HashMap<Integer , Integer > ();
    {
      Integer _count172 = _histogram170.getOrDefault(x, 0);
      _count172 = (_count172 + 1);
      _histogram170.put(x, _count172);

    }
    for (Integer _x167 : _var29) {
      if ((_histogram170.getOrDefault(_x167, 0) > 0)) {
        Integer _count173 = _histogram170.getOrDefault(_x167, 0);
        _count173 = (_count173 - 1);
        _histogram170.put(_x167, _count173);

      } else {
        Integer _count168 = _histogram166.getOrDefault(_x167, 0);
        _count168 = (_count168 + 1);
        _histogram166.put(_x167, _count168);

      }
    }
    for (Integer _var165 : _var29) {
      if ((_histogram166.getOrDefault(_var165, 0) > 0)) {
        Integer _count169 = _histogram166.getOrDefault(_var165, 0);
        _count169 = (_count169 - 1);
        _histogram166.put(_var165, _count169);

      } else {
        _var164.add(_var165);
      }
    }
    java.util.ArrayList<Integer > _var147 = _var164;
    java.util.ArrayList<Integer > _var174 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram176 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x177 : _var29) {
      Integer _count178 = _histogram176.getOrDefault(_x177, 0);
      _count178 = (_count178 + 1);
      _histogram176.put(_x177, _count178);

    }
    java.util.HashMap<Integer , Integer > _histogram180 = new java.util.HashMap<Integer , Integer > ();
    {
      Integer _count182 = _histogram180.getOrDefault(x, 0);
      _count182 = (_count182 + 1);
      _histogram180.put(x, _count182);

    }
    for (Integer _var175 : _var29) {
      if ((_histogram180.getOrDefault(_var175, 0) > 0)) {
        Integer _count183 = _histogram180.getOrDefault(_var175, 0);
        _count183 = (_count183 - 1);
        _histogram180.put(_var175, _count183);

      } else {
        if ((_histogram176.getOrDefault(_var175, 0) > 0)) {
          Integer _count179 = _histogram176.getOrDefault(_var175, 0);
          _count179 = (_count179 - 1);
          _histogram176.put(_var175, _count179);

        } else {
          _var174.add(_var175);
        }
      }
    }
    java.util.ArrayList<Integer > _var148 = _var174;
    for (Integer _var96 : _var147) {
      _var29.remove(_var96);
    }
    for (Integer _var96 : _var148) {
      _var29.add(_var96);
    }
  }
}

