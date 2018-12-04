public class TPCHQ5 implements java.io.Serializable {
  protected java.util.ArrayList<Lineitem > _var12490;
  public TPCHQ5() {
    clear();
  }

  public TPCHQ5(java.util.ArrayList<Lineitem > lineitems) {
    _var12490 = lineitems;
  }
  public void clear() {
    _var12490 = new java.util.ArrayList<Lineitem > ();
  }
  public void selectLineitems(String p1, Integer p2, Integer p3, java.util.function.Consumer<Float > _callback) {
    java.util.HashSet< Integer  > _distinct_elems20255 = new java.util.HashSet< Integer  > ();
    for (Lineitem _i20256 : _var12490) {
      {
        Integer _id20249 = ((((((_i20256).getVal()).supplier).getVal()).nation).getVal()).id;
        if ((!((_distinct_elems20255.contains(_id20249))))) {
          Float _sum20250 = 0f;
          for (Lineitem _i20254 : _var12490) {
            Boolean _v20257;
            Boolean _v20258;
            Boolean _v20259;
            Boolean _v20260;
            if ((((((_i20254).getVal()).order).getVal()).orderdate <= p3)) {
              _v20260 = (((((_i20254).getVal()).order).getVal()).orderdate >= p2);
            } else {
              _v20260 = false;
            }
            if (_v20260) {
              _v20259 = (java.util.Objects.equals(((((((((_i20254).getVal()).order).getVal()).customer).getVal()).nation).getVal()).id, ((((((_i20254).getVal()).supplier).getVal()).nation).getVal()).id));
            } else {
              _v20259 = false;
            }
            if (_v20259) {
              _v20258 = (java.util.Objects.equals(((((((((_i20254).getVal()).supplier).getVal()).nation).getVal()).region).getVal()).name, p1));
            } else {
              _v20258 = false;
            }
            if (_v20258) {
              _v20257 = (java.util.Objects.equals(((((((_i20254).getVal()).supplier).getVal()).nation).getVal()).id, _id20249));
            } else {
              _v20257 = false;
            }
            if (_v20257) {
              {
                {
                  {
                    _sum20250 = (_sum20250 + ((((_i20254).getVal()).extendedprice) * ((1.0f - ((_i20254).getVal()).discount))));
                  }
                }
              }
            }
          }
          {
            _callback.accept(_sum20250);
          }
          _distinct_elems20255.add(_id20249);
        }
      }
    }
  }
  public void insertLineitem(Lineitem i) {
    java.util.ArrayList<Lineitem > _var20261 = new java.util.ArrayList<Lineitem > ();
    java.util.HashMap<Lineitem , Integer > _histogram20263 = new java.util.HashMap<Lineitem , Integer > ();
    for (Lineitem _x20264 : _var12490) {
      Integer _count20265 = _histogram20263.getOrDefault(_x20264, 0);
      _count20265 = (_count20265 + 1);
      _histogram20263.put(_x20264, _count20265);

    }
    {
      Integer _count20265 = _histogram20263.getOrDefault(i, 0);
      _count20265 = (_count20265 + 1);
      _histogram20263.put(i, _count20265);

    }
    for (Lineitem _var20262 : _var12490) {
      if ((_histogram20263.getOrDefault(_var20262, 0) > 0)) {
        Integer _count20266 = _histogram20263.getOrDefault(_var20262, 0);
        _count20266 = (_count20266 - 1);
        _histogram20263.put(_var20262, _count20266);

      } else {
        _var20261.add(_var20262);
      }
    }
    java.util.ArrayList<Lineitem > _var20235 = _var20261;
    java.util.ArrayList<Lineitem > _var20267 = new java.util.ArrayList<Lineitem > ();
    java.util.HashMap<Lineitem , Integer > _histogram20269 = new java.util.HashMap<Lineitem , Integer > ();
    for (Lineitem _x20270 : _var12490) {
      Integer _count20271 = _histogram20269.getOrDefault(_x20270, 0);
      _count20271 = (_count20271 + 1);
      _histogram20269.put(_x20270, _count20271);

    }
    for (Lineitem _var20268 : _var12490) {
      if ((_histogram20269.getOrDefault(_var20268, 0) > 0)) {
        Integer _count20272 = _histogram20269.getOrDefault(_var20268, 0);
        _count20272 = (_count20272 - 1);
        _histogram20269.put(_var20268, _count20272);

      } else {
        _var20267.add(_var20268);
      }
    }
    {
      if ((_histogram20269.getOrDefault(i, 0) > 0)) {
        Integer _count20272 = _histogram20269.getOrDefault(i, 0);
        _count20272 = (_count20272 - 1);
        _histogram20269.put(i, _count20272);

      } else {
        _var20267.add(i);
      }
    }
    java.util.ArrayList<Lineitem > _var20236 = _var20267;
    for (Lineitem _var13058 : _var20235) {
      _var12490.remove(_var13058);
    }
    for (Lineitem _var13058 : _var20236) {
      _var12490.add(_var13058);
    }
  }
  public static class _Type20237 implements java.io.Serializable {
    private Integer id;
    private String name;
    public Integer  getId() { return id; }
    public String  getName() { return name; }
    public _Type20237(Integer id, String name) {
      this.id = id;
      this.name = name;
    }
    @Override
    public int hashCode() {
      int _hash_code20273 = 0;
      _hash_code20273 = (_hash_code20273 * 31) ^ ((id).hashCode());
      _hash_code20273 = (_hash_code20273 * 31) ^ ((name).hashCode());
      return _hash_code20273;
    }
    @Override
    public boolean equals(Object other) {
      if (other == null) return false;
      if (other == this) return true;
      if (!(other instanceof _Type20237)) return false;
      _Type20237 o = (_Type20237)other;
      Boolean _v20274;
      if ((java.util.Objects.equals(this.id, o.id))) {
        _v20274 = (java.util.Objects.equals(this.name, o.name));
      } else {
        _v20274 = false;
      }
      return _v20274;
    }
  }
  public static class Region extends _Type20237  implements java.io.Serializable {
    public _Type20237  getVal() { return this; }
    public Region(Integer _v20275, String _v20276) {
      super(_v20275, _v20276);
    }
  }
  public static class _Type20239 implements java.io.Serializable {
    private Integer id;
    private Region region;
    public Integer  getId() { return id; }
    public Region  getRegion() { return region; }
    public _Type20239(Integer id, Region region) {
      this.id = id;
      this.region = region;
    }
    @Override
    public int hashCode() {
      int _hash_code20277 = 0;
      _hash_code20277 = (_hash_code20277 * 31) ^ ((id).hashCode());
      _hash_code20277 = (_hash_code20277 * 31) ^ ((region).hashCode());
      return _hash_code20277;
    }
    @Override
    public boolean equals(Object other) {
      if (other == null) return false;
      if (other == this) return true;
      if (!(other instanceof _Type20239)) return false;
      _Type20239 o = (_Type20239)other;
      Boolean _v20278;
      if ((java.util.Objects.equals(this.id, o.id))) {
        _v20278 = (java.util.Objects.equals(this.region, o.region));
      } else {
        _v20278 = false;
      }
      return _v20278;
    }
  }
  public static class Nation extends _Type20239  implements java.io.Serializable {
    public _Type20239  getVal() { return this; }
    public Nation(Integer _v20279, Region _v20280) {
      super(_v20279, _v20280);
    }
  }
  public static class _Type20241 implements java.io.Serializable {
    private Integer id;
    private Nation nation;
    public Integer  getId() { return id; }
    public Nation  getNation() { return nation; }
    public _Type20241(Integer id, Nation nation) {
      this.id = id;
      this.nation = nation;
    }
    @Override
    public int hashCode() {
      int _hash_code20281 = 0;
      _hash_code20281 = (_hash_code20281 * 31) ^ ((id).hashCode());
      _hash_code20281 = (_hash_code20281 * 31) ^ ((nation).hashCode());
      return _hash_code20281;
    }
    @Override
    public boolean equals(Object other) {
      if (other == null) return false;
      if (other == this) return true;
      if (!(other instanceof _Type20241)) return false;
      _Type20241 o = (_Type20241)other;
      Boolean _v20282;
      if ((java.util.Objects.equals(this.id, o.id))) {
        _v20282 = (java.util.Objects.equals(this.nation, o.nation));
      } else {
        _v20282 = false;
      }
      return _v20282;
    }
  }
  public static class Supplier extends _Type20241  implements java.io.Serializable {
    public _Type20241  getVal() { return this; }
    public Supplier(Integer _v20283, Nation _v20284) {
      super(_v20283, _v20284);
    }
  }
  public static class Customer extends _Type20241  implements java.io.Serializable {
    public _Type20241  getVal() { return this; }
    public Customer(Integer _v20285, Nation _v20286) {
      super(_v20285, _v20286);
    }
  }
  public static class _Type20244 implements java.io.Serializable {
    private Integer id;
    private Integer orderdate;
    private Customer customer;
    public Integer  getId() { return id; }
    public Integer  getOrderdate() { return orderdate; }
    public Customer  getCustomer() { return customer; }
    public _Type20244(Integer id, Integer orderdate, Customer customer) {
      this.id = id;
      this.orderdate = orderdate;
      this.customer = customer;
    }
    @Override
    public int hashCode() {
      int _hash_code20287 = 0;
      _hash_code20287 = (_hash_code20287 * 31) ^ ((id).hashCode());
      _hash_code20287 = (_hash_code20287 * 31) ^ ((orderdate).hashCode());
      _hash_code20287 = (_hash_code20287 * 31) ^ ((customer).hashCode());
      return _hash_code20287;
    }
    @Override
    public boolean equals(Object other) {
      if (other == null) return false;
      if (other == this) return true;
      if (!(other instanceof _Type20244)) return false;
      _Type20244 o = (_Type20244)other;
      Boolean _v20288;
      if ((java.util.Objects.equals(this.id, o.id))) {
        Boolean _v20289;
        if ((java.util.Objects.equals(this.orderdate, o.orderdate))) {
          _v20289 = (java.util.Objects.equals(this.customer, o.customer));
        } else {
          _v20289 = false;
        }
        _v20288 = _v20289;
      } else {
        _v20288 = false;
      }
      return _v20288;
    }
  }
  public static class Order extends _Type20244  implements java.io.Serializable {
    public _Type20244  getVal() { return this; }
    public Order(Integer _v20290, Integer _v20291, Customer _v20292) {
      super(_v20290, _v20291, _v20292);
    }
  }
  public static class _Type20246 implements java.io.Serializable {
    private Integer id;
    private Float extendedprice;
    private Float discount;
    private Supplier supplier;
    private Order order;
    public Integer  getId() { return id; }
    public Float  getExtendedprice() { return extendedprice; }
    public Float  getDiscount() { return discount; }
    public Supplier  getSupplier() { return supplier; }
    public Order  getOrder() { return order; }
    public _Type20246(Integer id, Float extendedprice, Float discount, Supplier supplier, Order order) {
      this.id = id;
      this.extendedprice = extendedprice;
      this.discount = discount;
      this.supplier = supplier;
      this.order = order;
    }
    @Override
    public int hashCode() {
      int _hash_code20293 = 0;
      _hash_code20293 = (_hash_code20293 * 31) ^ ((id).hashCode());
      _hash_code20293 = (_hash_code20293 * 31) ^ ((extendedprice).hashCode());
      _hash_code20293 = (_hash_code20293 * 31) ^ ((discount).hashCode());
      _hash_code20293 = (_hash_code20293 * 31) ^ ((supplier).hashCode());
      _hash_code20293 = (_hash_code20293 * 31) ^ ((order).hashCode());
      return _hash_code20293;
    }
    @Override
    public boolean equals(Object other) {
      if (other == null) return false;
      if (other == this) return true;
      if (!(other instanceof _Type20246)) return false;
      _Type20246 o = (_Type20246)other;
      Boolean _v20294;
      Boolean _v20295;
      if ((java.util.Objects.equals(this.id, o.id))) {
        _v20295 = (java.util.Objects.equals(this.extendedprice, o.extendedprice));
      } else {
        _v20295 = false;
      }
      if (_v20295) {
        Boolean _v20296;
        if ((java.util.Objects.equals(this.discount, o.discount))) {
          Boolean _v20297;
          if ((java.util.Objects.equals(this.supplier, o.supplier))) {
            _v20297 = (java.util.Objects.equals(this.order, o.order));
          } else {
            _v20297 = false;
          }
          _v20296 = _v20297;
        } else {
          _v20296 = false;
        }
        _v20294 = _v20296;
      } else {
        _v20294 = false;
      }
      return _v20294;
    }
  }
  public static class Lineitem extends _Type20246  implements java.io.Serializable {
    public _Type20246  getVal() { return this; }
    public Lineitem(Integer _v20298, Float _v20299, Float _v20300, Supplier _v20301, Order _v20302) {
      super(_v20298, _v20299, _v20300, _v20301, _v20302);
    }
  }
}

