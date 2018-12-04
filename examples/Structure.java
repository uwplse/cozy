public class Structure implements java.io.Serializable {
  protected Integer _var14;
  public Structure() {
    clear();
  }

  public Structure(Integer x) {
    _var14 = x;
  }
  public void clear() {
    _var14 = 0;
  }
  public Integer foo() {
    return ((_var14) + 1);
  }
  public void setX(Integer y) {
    _var14 = y;
  }
}

