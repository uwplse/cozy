import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.concurrent.ThreadLocalRandom;

class LSortMain {
  public static void main(String[] args) {
    ArrayList<Integer> arr = new ArrayList<Integer>();
    Integer N_SIZE  = 10000;
    ArrayList<Integer> to_add = new ArrayList<Integer>();
    ArrayList<Integer> to_rm = new ArrayList<Integer>();
    for (int i = 0; i < N_SIZE; i++) {
      arr.add(ThreadLocalRandom.current().nextInt(0, N_SIZE * 2));
    }
    for (int i = 0; i < N_SIZE; i++) {
      to_add.add(ThreadLocalRandom.current().nextInt(0, N_SIZE * 3));
      to_rm.add(ThreadLocalRandom.current().nextInt(0, N_SIZE * 3));
    }
    LSort b = new LSort(arr); // cozy generated
    Collections.sort(arr);

    long lStartTime = System.nanoTime();
    for (int i = 0; i < N_SIZE; i++) {
      b.add(to_add.get(i));
      b.rm(to_rm.get(i));
    }
    System.out.println("Synthesized code time in ms: " + (System.nanoTime() - lStartTime) / 1000000);

    lStartTime = System.nanoTime();
    for (int i = 0; i < N_SIZE; i++) {
      arr.add(to_add.get(i));
      arr.remove(to_rm.get(i));
      Collections.sort(arr);
    }
    System.out.println("Baseline code time in ms: " + (System.nanoTime() - lStartTime) / 1000000);
  }
}
