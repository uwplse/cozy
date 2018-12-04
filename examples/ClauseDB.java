public class ClauseDB implements java.io.Serializable {
  protected java.util.ArrayList<Integer > _var58;
  public ClauseDB() {
    clear();
  }

  public ClauseDB(java.util.ArrayList<Integer > ints) {
    _var58 = ints;
  }
  public void clear() {
    _var58 = new java.util.ArrayList<Integer > ();
  }
  public Boolean contains(Integer i) {
    Boolean _found185 = false;
    _label187: do {
      for (Integer _x186 : _var58) {
        if ((java.util.Objects.equals(_x186, i))) {
          _found185 = true;
          break _label187;
        }
      }
    } while (false);
    return _found185;
  }
  public Integer size() {
    Integer _sum188 = 0;
    for (Integer _x190 : _var58) {
      {
        _sum188 = (_sum188 + 1);
      }
    }
    return _sum188;
  }
  public void add(Integer i) {
    java.util.ArrayList<Integer > _var191 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram193 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x194 : _var58) {
      Integer _count195 = _histogram193.getOrDefault(_x194, 0);
      _count195 = (_count195 + 1);
      _histogram193.put(_x194, _count195);

    }
    {
      Integer _count195 = _histogram193.getOrDefault(i, 0);
      _count195 = (_count195 + 1);
      _histogram193.put(i, _count195);

    }
    for (Integer _var192 : _var58) {
      if ((_histogram193.getOrDefault(_var192, 0) > 0)) {
        Integer _count196 = _histogram193.getOrDefault(_var192, 0);
        _count196 = (_count196 - 1);
        _histogram193.put(_var192, _count196);

      } else {
        _var191.add(_var192);
      }
    }
    java.util.ArrayList<Integer > _var181 = _var191;
    java.util.ArrayList<Integer > _var197 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram199 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x200 : _var58) {
      Integer _count201 = _histogram199.getOrDefault(_x200, 0);
      _count201 = (_count201 + 1);
      _histogram199.put(_x200, _count201);

    }
    for (Integer _var198 : _var58) {
      if ((_histogram199.getOrDefault(_var198, 0) > 0)) {
        Integer _count202 = _histogram199.getOrDefault(_var198, 0);
        _count202 = (_count202 - 1);
        _histogram199.put(_var198, _count202);

      } else {
        _var197.add(_var198);
      }
    }
    {
      if ((_histogram199.getOrDefault(i, 0) > 0)) {
        Integer _count202 = _histogram199.getOrDefault(i, 0);
        _count202 = (_count202 - 1);
        _histogram199.put(i, _count202);

      } else {
        _var197.add(i);
      }
    }
    java.util.ArrayList<Integer > _var182 = _var197;
    for (Integer _var79 : _var181) {
      _var58.remove(_var79);
    }
    for (Integer _var79 : _var182) {
      _var58.add(_var79);
    }
  }
  public void remove(Integer i) {
    java.util.ArrayList<Integer > _var203 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram205 = new java.util.HashMap<Integer , Integer > ();
    java.util.HashMap<Integer , Integer > _histogram209 = new java.util.HashMap<Integer , Integer > ();
    {
      Integer _count211 = _histogram209.getOrDefault(i, 0);
      _count211 = (_count211 + 1);
      _histogram209.put(i, _count211);

    }
    for (Integer _x206 : _var58) {
      if ((_histogram209.getOrDefault(_x206, 0) > 0)) {
        Integer _count212 = _histogram209.getOrDefault(_x206, 0);
        _count212 = (_count212 - 1);
        _histogram209.put(_x206, _count212);

      } else {
        Integer _count207 = _histogram205.getOrDefault(_x206, 0);
        _count207 = (_count207 + 1);
        _histogram205.put(_x206, _count207);

      }
    }
    for (Integer _var204 : _var58) {
      if ((_histogram205.getOrDefault(_var204, 0) > 0)) {
        Integer _count208 = _histogram205.getOrDefault(_var204, 0);
        _count208 = (_count208 - 1);
        _histogram205.put(_var204, _count208);

      } else {
        _var203.add(_var204);
      }
    }
    java.util.ArrayList<Integer > _var183 = _var203;
    java.util.ArrayList<Integer > _var213 = new java.util.ArrayList<Integer > ();
    java.util.HashMap<Integer , Integer > _histogram215 = new java.util.HashMap<Integer , Integer > ();
    for (Integer _x216 : _var58) {
      Integer _count217 = _histogram215.getOrDefault(_x216, 0);
      _count217 = (_count217 + 1);
      _histogram215.put(_x216, _count217);

    }
    java.util.HashMap<Integer , Integer > _histogram219 = new java.util.HashMap<Integer , Integer > ();
    {
      Integer _count221 = _histogram219.getOrDefault(i, 0);
      _count221 = (_count221 + 1);
      _histogram219.put(i, _count221);

    }
    for (Integer _var214 : _var58) {
      if ((_histogram219.getOrDefault(_var214, 0) > 0)) {
        Integer _count222 = _histogram219.getOrDefault(_var214, 0);
        _count222 = (_count222 - 1);
        _histogram219.put(_var214, _count222);

      } else {
        if ((_histogram215.getOrDefault(_var214, 0) > 0)) {
          Integer _count218 = _histogram215.getOrDefault(_var214, 0);
          _count218 = (_count218 - 1);
          _histogram215.put(_var214, _count218);

        } else {
          _var213.add(_var214);
        }
      }
    }
    java.util.ArrayList<Integer > _var184 = _var213;
    for (Integer _var156 : _var183) {
      _var58.remove(_var156);
    }
    for (Integer _var156 : _var184) {
      _var58.add(_var156);
    }
  }
}

