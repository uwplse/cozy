import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.concurrent.ThreadLocalRandom;

class MaxBagMain {
  public static void main(String[] args) {
    MaxBag b = new MaxBag(); // cozy generated
    HashSet<Integer> s = new HashSet<Integer>(); // baseline
    Integer N = 10000;
    Integer M = 1000000;

    ArrayList<Integer> to_add = new ArrayList<Integer>();
    ArrayList<Integer> to_delete = new ArrayList<Integer>();
    ArrayList<Integer> max_bs = new ArrayList<Integer>();
    ArrayList<Integer> max_ss = new ArrayList<Integer>();

    for (int i = 0; i < N; i++) {
      to_add.add(ThreadLocalRandom.current().nextInt(0, M));
      to_delete.add(ThreadLocalRandom.current().nextInt(0, M));
    }

    long lStartTime = System.nanoTime();
    for (int i = 0; i < N; i++) {
      b.add(to_add.get(i));
    }

    for (int i = 0; i < N; i++) {
      b.remove(to_delete.get(i));
      max_bs.add(b.get_max());
    }
    System.out.println("Synthesized code time in ms: " + (System.nanoTime() - lStartTime) / 1000000);
    
    lStartTime = System.nanoTime();
    for (int i = 0; i < N; i++) {
      s.add(to_add.get(i));
    }

    for (int i = 0; i < N; i++) {
      s.remove(to_delete.get(i));
      max_ss.add(Collections.max(s));
    }

    System.out.println("Baseline code time in ms: " + (System.nanoTime() - lStartTime) / 1000000);

    for (int i = 0; i < N; i++) {
      assert max_bs.get(i) == max_ss.get(i);
    }
  }
}
