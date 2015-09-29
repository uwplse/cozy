package tests;

import java.util.*;

public class BinarySearch {

    public static <T> List<T> list(Iterator<T> it) {
        List<T> l = new ArrayList<>();
        it.forEachRemaining(l::add);
        return l;
    }

    public static void viz(DataStructure.Record r, String indent, Set<DataStructure.Record> seen) {
        if (r == null) { System.out.println((Object)null); return; }
        if (seen.contains(r)) { System.out.println("<<recursive>>"); return; }
        seen.add(r);
        System.out.println(r);
        indent += "  ";
        System.out.println(indent + "P: " + r._parent5);
        System.out.print(indent + "L: "); viz(r._left3, indent, seen);
        System.out.print(indent + "R: "); viz(r._right4, indent, seen);
        seen.remove(r);
    }

    public static void main(String[] args) {

        DataStructure ds = new DataStructure();

        DataStructure.Record r1 = new DataStructure.Record(1.0);
        DataStructure.Record r2 = new DataStructure.Record(2.0);
        DataStructure.Record r3 = new DataStructure.Record(3.0);
        DataStructure.Record r4 = new DataStructure.Record(3.1);

        ds.add(r1);
        ds.add(r2);
        ds.add(r3);
        ds.add(r4);

        Iterator<DataStructure.Record> i;

        i = ds.q(1.5, 2.5);
        System.out.print("Test 1: [ ");
        while (i.hasNext()) {
            System.out.print(i.next());
            System.out.print(' ');
        }
        System.out.println(']');
        assert list(ds.q(1.5, 2.5)).equals(Arrays.asList(r2));

        // viz(ds._name1, "", new HashSet<>());
        ds.remove(r3);
        // viz(ds._name1, "", new HashSet<>());

        i = ds.q(0.0, 5.0);
        System.out.print("Test 2: [ ");
        while (i.hasNext()) {
            System.out.print(i.next());
            System.out.print(' ');
        }
        System.out.println(']');
        assert list(ds.q(0.0, 5.0)).equals(Arrays.asList(r1, r2, r4));

    }

}
