public class DataStructure implements java.io.Serializable {
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
    /*private*/ static class _Tuple8 implements java.io.Serializable {
        String name;
        @Override
        public int hashCode() {
            int hc = 0;
            hc = 31 * hc + name.hashCode();
            return hc;
        }
        @Override
        public boolean equals(Object other) {
            if (other == null) return false;
            if (other.getClass() != getClass()) return false;
            _Tuple8 x = (_Tuple8)other;
            if (!((x.name) == (name))) return false;
            return true;
        }
    }
    /*private*/ static class _Tuple7 implements java.io.Serializable {
        Record _head1;
        @Override
        public int hashCode() {
            int hc = 0;
            hc = 31 * hc + _head1.hashCode();
            return hc;
        }
        @Override
        public boolean equals(Object other) {
            if (other == null) return false;
            if (other.getClass() != getClass()) return false;
            _Tuple7 x = (_Tuple7)other;
            if (!((x._head1) == (_head1))) return false;
            return true;
        }
    }
  public DataStructure() {
    _node9 = new Node(false);
    _length10 = 4;
      }
  public void add(Record x) {
    String _key11;
    _key11 = (x).name;
    int _hashcode12 = (_key11).hashCode();
    Node _node13 = _node9;
    int _level14 = 0;
    while ((_level14) <= (8)) {
    Node _match15 = _match15.getMatchNode(_hashcode12, length * i, length);
    if ((_match15) == null) {
    break;
    }
    _node13 = _match15;
    _level14++;
    }
    while ((_level14) <= (8)) {
    Node _node16;
    if (INTEGER_BIT_LENGTH % length == 0 && i == INTEGER_BIT_LENGTH / length) {
    _node16 = new Node(true);
    } else {
    _node16 = new Node(false);
    }
    _node13.addSignature(_hashcode12, i * length, length);
    _node13.next.add(_node16);
    _node13 = _node16;
    _level14++;
    }
    _node13.add(x)
      }
  public void remove(Record x) {
    String _key18;
    _key18 = (x).name;
    _hashcode17 = (_key18).hashCode();
    Node _node19 = _node9;
    int _level20 = 0;
    while ((_level20) <= (8)) {
    Node _match21 = _match21.getMatchNode(_hashcode17, length * i, length);
    if ((_match21) == null) {
    return;
    }
    _node19 = _match21;
    _level20++;
    }
    _node19.remove(_key18)
      }
