public class Graph implements java.io.Serializable {
  protected java.util.ArrayList<Edge > _var268;
  public Graph() {
    clear();
  }

  public Graph(java.util.ArrayList<Node > nodes, java.util.ArrayList<Edge > edges) {
    _var268 = edges;
  }
  public void clear() {
    _var268 = new java.util.ArrayList<Edge > ();
  }
  public Integer out_degree(Integer nodeId) {
    Integer _sum1382 = 0;
    for (Edge _e1385 : _var268) {
      if ((java.util.Objects.equals(((_e1385).getVal()).src, nodeId))) {
        {
          {
            _sum1382 = (_sum1382 + 1);
          }
        }
      }
    }
    return _sum1382;
  }
  public void addNode(Node n) {
  }
  public void addEdge(Edge e) {
    java.util.ArrayList<Edge > _var1386 = new java.util.ArrayList<Edge > ();
    java.util.HashMap<Edge , Integer > _histogram1388 = new java.util.HashMap<Edge , Integer > ();
    for (Edge _x1389 : _var268) {
      Integer _count1390 = _histogram1388.getOrDefault(_x1389, 0);
      _count1390 = (_count1390 + 1);
      _histogram1388.put(_x1389, _count1390);

    }
    {
      Integer _count1390 = _histogram1388.getOrDefault(e, 0);
      _count1390 = (_count1390 + 1);
      _histogram1388.put(e, _count1390);

    }
    for (Edge _var1387 : _var268) {
      if ((_histogram1388.getOrDefault(_var1387, 0) > 0)) {
        Integer _count1391 = _histogram1388.getOrDefault(_var1387, 0);
        _count1391 = (_count1391 - 1);
        _histogram1388.put(_var1387, _count1391);

      } else {
        _var1386.add(_var1387);
      }
    }
    java.util.ArrayList<Edge > _var1376 = _var1386;
    java.util.ArrayList<Edge > _var1392 = new java.util.ArrayList<Edge > ();
    java.util.HashMap<Edge , Integer > _histogram1394 = new java.util.HashMap<Edge , Integer > ();
    for (Edge _x1395 : _var268) {
      Integer _count1396 = _histogram1394.getOrDefault(_x1395, 0);
      _count1396 = (_count1396 + 1);
      _histogram1394.put(_x1395, _count1396);

    }
    for (Edge _var1393 : _var268) {
      if ((_histogram1394.getOrDefault(_var1393, 0) > 0)) {
        Integer _count1397 = _histogram1394.getOrDefault(_var1393, 0);
        _count1397 = (_count1397 - 1);
        _histogram1394.put(_var1393, _count1397);

      } else {
        _var1392.add(_var1393);
      }
    }
    {
      if ((_histogram1394.getOrDefault(e, 0) > 0)) {
        Integer _count1397 = _histogram1394.getOrDefault(e, 0);
        _count1397 = (_count1397 - 1);
        _histogram1394.put(e, _count1397);

      } else {
        _var1392.add(e);
      }
    }
    java.util.ArrayList<Edge > _var1377 = _var1392;
    for (Edge _var458 : _var1376) {
      _var268.remove(_var458);
    }
    for (Edge _var458 : _var1377) {
      _var268.add(_var458);
    }
  }
  public static class _Type1378 implements java.io.Serializable {
    private Integer id;
    public Integer  getId() { return id; }
    public _Type1378(Integer id) {
      this.id = id;
    }
    @Override
    public int hashCode() {
      int _hash_code1398 = 0;
      _hash_code1398 = (_hash_code1398 * 31) ^ ((id).hashCode());
      return _hash_code1398;
    }
    @Override
    public boolean equals(Object other) {
      if (other == null) return false;
      if (other == this) return true;
      if (!(other instanceof _Type1378)) return false;
      _Type1378 o = (_Type1378)other;
      return (java.util.Objects.equals(this.id, o.id));
    }
  }
  public static class Node extends _Type1378  implements java.io.Serializable {
    public _Type1378  getVal() { return this; }
    public Node(Integer _v1399) {
      super(_v1399);
    }
  }
  public static class _Type1380 implements java.io.Serializable {
    private Integer src;
    private Integer dst;
    public Integer  getSrc() { return src; }
    public Integer  getDst() { return dst; }
    public _Type1380(Integer src, Integer dst) {
      this.src = src;
      this.dst = dst;
    }
    @Override
    public int hashCode() {
      int _hash_code1400 = 0;
      _hash_code1400 = (_hash_code1400 * 31) ^ ((src).hashCode());
      _hash_code1400 = (_hash_code1400 * 31) ^ ((dst).hashCode());
      return _hash_code1400;
    }
    @Override
    public boolean equals(Object other) {
      if (other == null) return false;
      if (other == this) return true;
      if (!(other instanceof _Type1380)) return false;
      _Type1380 o = (_Type1380)other;
      Boolean _v1401;
      if ((java.util.Objects.equals(this.src, o.src))) {
        _v1401 = (java.util.Objects.equals(this.dst, o.dst));
      } else {
        _v1401 = false;
      }
      return _v1401;
    }
  }
  public static class Edge extends _Type1380  implements java.io.Serializable {
    public _Type1380  getVal() { return this; }
    public Edge(Integer _v1402, Integer _v1403) {
      super(_v1402, _v1403);
    }
  }
}

