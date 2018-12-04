public class BoundsBug2 implements java.io.Serializable {
  protected Boolean _var14;
  public BoundsBug2() {
    clear();
  }

  public BoundsBug2(Integer executions, Boolean bugHappened) {
    _var14 = bugHappened;
  }
  public void clear() {
    _var14 = false;
  }
  public Boolean didBugHappen() {
    return _var14;
  }
  public void exec() {
  }
}

