package tests;

import java.util.*;

public class Intervals1 {

    public static <T> List<T> list(Iterator<T> it) {
        List<T> l = new ArrayList<>();
        it.forEachRemaining(l::add);
        return l;
    }

    public static <T> Set<T> set(Iterator<T> it) {
        Set<T> l = new HashSet<>();
        it.forEachRemaining(l::add);
        return l;
    }

    private static String dumpstate(DataStructure.q_iterator it) {
        return "cursor = " + it._cursor3;
    }

    private static void debugq(DataStructure s, double v) {

        DataStructure.q_iterator it = (DataStructure.q_iterator)s.q(v);

        System.out.println("debugging " + v + "...");
        while (true) {

            System.out.print("    " + dumpstate(it));
            boolean hn = it.hasNext();
            System.out.println("; hasNext=" + hn);
            if (!hn) {
                break;
            }
            DataStructure.Record r = it.next();
            System.out.println("    yielded " + r);

        }

    }

    public static void main(String[] args) {

        DataStructure ds = new DataStructure();

        DataStructure.Record r1 = new DataStructure.Record(1, 2, "r1");
        DataStructure.Record r2 = new DataStructure.Record(1, 4, "r2");
        DataStructure.Record r3 = new DataStructure.Record(2, 3, "r3");
        DataStructure.Record r4 = new DataStructure.Record(3, 5, "r4");

        ds.add(r1);
        ds.add(r2);
        ds.add(r3);
        ds.add(r4);

        debugq(ds, 0);
        assert set(ds.q(0)).equals(Collections.emptySet());

        debugq(ds, 5);
        assert set(ds.q(5)).equals(new HashSet<>(Arrays.asList(r4)));

        debugq(ds, 1.1);
        assert set(ds.q(1.1)).equals(new HashSet<>(Arrays.asList(r1, r2)));

        debugq(ds, 1);
        assert set(ds.q(1)).equals(new HashSet<>(Arrays.asList(r1, r2)));

        debugq(ds, 3);
        assert set(ds.q(3)).equals(new HashSet<>(Arrays.asList(r2, r3, r4)));

    }

}
