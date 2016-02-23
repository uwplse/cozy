public class DataStructureHamt implements java.io.Serializable {
    public static class Record implements java.io.Serializable {
        private static final long serialVersionUID = 1L;
        /*private*/ String name;
        public String getName() { return name; }
        /*private*/ Record _next2;
        /*private*/ Record _prev3;
        public Record(String name) {
            this.name = name;
        }
        @Override
        public String toString() {
            return new StringBuilder().append("Record(").append("name=").append(name).append(')').toString();
        }
    }
    /*private*/ static class _Tuple9 implements java.io.Serializable {
        java.util.List<_Tuple9> next;
        java.util.List<Record> values;
        boolean isLeaf;
        int signature;
        @Override
        public int hashCode() {
            int hc = 0;
            hc = 31 * hc + next.hashCode();
            hc = 31 * hc + values.hashCode();
            hc = 31 * hc + 1231;
            hc = 31 * hc + signature;
            return hc;
        }
        @Override
        public boolean equals(Object other) {
            if (other == null) return false;
            if (other.getClass() != getClass()) return false;
            _Tuple9 x = (_Tuple9)other;
            if (!((x.next) == (next))) return false;
            if (!((x.values) == (values))) return false;
            if (!((x.isLeaf) == (isLeaf))) return false;
            if (!((x.signature) == (signature))) return false;
            return true;
        }
    }
    public DataStructureHamt() {
        _node10 = new _Tuple9();
        _node10.isLeaf = false;
        _node10.next = new java.util.LinkedList<_Tuple9>();
        int _index12 = 0;
        while ((_index12) < (16)) {
            (_node10.next).add(null);
            _index12++;
        }
        _node10.signature = 0;
        _length11 = 4;
    }
    public void add(Record x) {
        String _key13;
        _key13 = (x).name;
        int _hashcode14 = (_key13).hashCode();
        _Tuple9 _node15 = _node10;
        int _level16 = 0;
        while ((_level16) <= (8)) {
            _Tuple9 _match17;
            int _bits18 = 0;
            boolean _isMatch19;
            if (_node15.isLeaf) {
                _isMatch19 = false;
            } else {
                _bits18 = ((((_hashcode14) << ((_length11) * (_level16)))) >>> ((32 - _length11)));
                _isMatch19 = (1) == (((((_node15.signature) >>> (_bits18))) & (1)));
            }
            if (!(_isMatch19)) {
                _match17 = null;
            } else {
                _match17 = _node15.next.get(_bits18);
            }
            if ((_match17) == null) {
                break;
            }
            _node15 = _match17;
            _level16++;
        }
        while ((_level16) <= (8)) {
            int _bit21 = 0;
            _Tuple9 _node20;
            if ((_level16) < (8)) {
                _node20 = new _Tuple9();
                _node20.isLeaf = false;
                _node20.next = new java.util.LinkedList<_Tuple9>();
                int _index22 = 0;
                while ((_index22) < (16)) {
                    (_node20.next).add(null);
                    _index22++;
                }
                _node20.signature = 0;
            } else {
                _node20 = new _Tuple9();
                _node20.isLeaf = true;
                _node20.values = new java.util.LinkedList<Record>();
                _node20.signature = 0;
            }
            if (_node15.isLeaf) {
                return;
            }
            boolean _isMatch23;
            if (_node15.isLeaf) {
                _isMatch23 = false;
            } else {
                _bit21 = ((((_hashcode14) << ((_length11) * (_level16)))) >>> ((32 - _length11)));
                _isMatch23 = (1) == (((((_node15.signature) >>> (_bit21))) & (1)));
            }
            if (_isMatch23) {
                return;
            }
            _node15.signature = ((_node15.signature) | (((1) << (_bit21))));
            (_node15.next).set(_bit21, _node20);
            (_node15.next).add(_node20);
            _node15 = _node20;
            _level16++;
        }
        Record _handle24 = null;
        int _index25 = 0;
        while ((_index25) < ((_node15.values).size())) {
            Record _sub26 = (_node15.values).get(_index25);
            if (((_sub26).name).equals(_key13)) {
                _handle24 = _sub26;
                boolean _name27 = (_node15.values).remove(_sub26);
                break;
            }
        }
        (x)._prev3 = null;
        (x)._next2 = _handle24;
        if (!((_handle24) == null)) {
            (_handle24)._prev3 = x;
        }
        _handle24 = x;
        (_node15.values).add(x);
    }
    public void remove(Record x) {
        int _hashcode28;
        String _key29;
        _key29 = (x).name;
        _hashcode28 = (_key29).hashCode();
        _Tuple9 _node30 = _node10;
        int _level31 = 0;
        while ((_level31) <= (8)) {
            _Tuple9 _match32;
            int _bits33 = 0;
            boolean _isMatch34;
            if (_node30.isLeaf) {
                _isMatch34 = false;
            } else {
                _bits33 = ((((_hashcode28) << ((_length11) * (_level31)))) >>> ((32 - _length11)));
                _isMatch34 = (1) == (((((_node30.signature) >>> (_bits33))) & (1)));
            }
            if (!(_isMatch34)) {
                _match32 = null;
            } else {
                _match32 = _node30.next.get(_bits33);
            }
            if ((_match32) == null) {
                return;
            }
            _node30 = _match32;
            _level31++;
        }
        boolean _name35;
        Record _handle36 = null;
        int _index37 = 0;
        while ((_index37) < ((_node30.values).size())) {
            Record _sub38 = (_node30.values).get(_index37);
            if (((_sub38).name).equals(_key29)) {
                _handle36 = _sub38;
                boolean _name39 = (_node30.values).remove(_sub38);
                break;
            }
        }
    }
    /*private*/ _Tuple9 _node10;
    /*private*/ int _length11;
    /*private*/ static final class q_iterator implements java.util.Iterator<Record> {
        DataStructureHamt parent;
        Record _prev_cursor4;
        Record _cursor5;
        q_iterator(DataStructureHamt parent, Record _prev_cursor4, Record _cursor5) {
          this.parent = parent;
          this._prev_cursor4 = _prev_cursor4;
          this._cursor5 = _cursor5;
      }
      @Override public boolean hasNext() {
        return !((_cursor5) == null);
    }
    @Override public Record next() {
      _prev_cursor4 = _cursor5;
      _cursor5 = (_cursor5)._next2;
      return _prev_cursor4;
  }
  @Override public void remove() {
      String _key40;
      _key40 = (_cursor5).name;
      Record _maphandle41;
      _maphandle41 = (parent)._map6.get(_key40);
      Record _substructure42 = _maphandle41;
      Record _old_prev43 = _prev_cursor4;
      if ((_prev_cursor4) == (_substructure42)) {
          _substructure42 = (_prev_cursor4)._next2;
      }
      if (!(((_prev_cursor4)._next2) == null)) {
          ((_prev_cursor4)._next2)._prev3 = (_prev_cursor4)._prev3;
      }
      if (!(((_prev_cursor4)._prev3) == null)) {
          ((_prev_cursor4)._prev3)._next2 = (_prev_cursor4)._next2;
      }
      (_prev_cursor4)._prev3 = null;
      (_prev_cursor4)._next2 = null;
      _prev_cursor4 = null;
      (parent)._map6.put(_key40, _substructure42);
  }
}
public java.util.Iterator<Record> q(String expectedName) {
    String _key44;
    int _hashcode45;
    Record __prev_cursor446 = null;
    Record __cursor547 = null;
    _key44 = expectedName;
    _hashcode45 = (_key44).hashCode();
    _Tuple9 _node48 = _node10;
    int _level49 = 0;
    while ((_level49) <= (8)) {
        _Tuple9 _match50;
        int _bits51 = 0;
        boolean _isMatch52;
        if (_node48.isLeaf) {
            _isMatch52 = false;
        } else {
            _bits51 = ((((_hashcode45) << ((_length11) * (_level49)))) >>> ((32 - _length11)));
            _isMatch52 = (1) == (((((_node48.signature) >>> (_bits51))) & (1)));
        }
        if (!(_isMatch52)) {
            _match50 = null;
        } else {
            _match50 = _node48.next.get(_bits51);
        }
        if ((_match50) == null) {
            __prev_cursor446 = null;
            __cursor547 = null;
            break;
        }
        _node48 = _match50;
        _level49++;
    }
    if (!((_node48) == null)) {
        Record _handle53 = null;
        int _index54 = 0;
        while ((_index54) < ((_node48.values).size())) {
            Record _sub55 = (_node48.values).get(_index54);
            if (((_sub55).name).equals(_key44)) {
                _handle53 = _sub55;
                boolean _name56 = (_node48.values).remove(_sub55);
                break;
            }
        }
        if (_handle53 != null) {
            Record _substructure57 = _handle53;
            __prev_cursor446 = null;
            __cursor547 = _substructure57;
        } else {
            __prev_cursor446 = null;
            __cursor547 = null;
        }
    }
    return new q_iterator(this, __prev_cursor446, __cursor547);  }
}
