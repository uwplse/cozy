public class In implements java.io.Serializable {
  protected java.util.ArrayList<Elem > _var50;
  public In() {
    clear();
  }

  public In(java.util.ArrayList<Elem > xs) {
    _var50 = xs;
  }
  public void clear() {
    _var50 = new java.util.ArrayList<Elem > ();
  }
  public void a(Integer st, Integer ed, java.util.function.Consumer<Elem > _callback) {
    for (Elem _x55 : _var50) {
      Boolean _v56;
      if ((java.util.Objects.equals(((_x55).getVal())._1, ed))) {
        _v56 = (java.util.Objects.equals(((_x55).getVal())._0, st));
      } else {
        _v56 = false;
      }
      if (_v56) {
        {
          {
            _callback.accept(_x55);
          }
        }
      }
    }
  }
  public static class _Type51 implements java.io.Serializable {
    private Integer _0;
    private Integer _1;
    public Integer  get_0() { return _0; }
    public Integer  get_1() { return _1; }
    public _Type51(Integer _0, Integer _1) {
      this._0 = _0;
      this._1 = _1;
    }
    @Override
    public int hashCode() {
      int _hash_code57 = 0;
      _hash_code57 = (_hash_code57 * 31) ^ ((_0).hashCode());
      _hash_code57 = (_hash_code57 * 31) ^ ((_1).hashCode());
      return _hash_code57;
    }
    @Override
    public boolean equals(Object other) {
      if (other == null) return false;
      if (other == this) return true;
      if (!(other instanceof _Type51)) return false;
      _Type51 o = (_Type51)other;
      Boolean _v58;
      if ((java.util.Objects.equals(this._0, o._0))) {
        _v58 = (java.util.Objects.equals(this._1, o._1));
      } else {
        _v58 = false;
      }
      return _v58;
    }
  }
  public static class Elem implements java.io.Serializable {
    private _Type51 val;
    public _Type51  getVal() { return val; }
    public Elem(Integer _v59, Integer _v60) {
      this.val = new _Type51(_v59, _v60);
    }
  }
}

