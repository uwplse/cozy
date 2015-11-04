package tests;

import java.util.*;

public class BinarySearch {

    public static <T> List<T> list(Iterator<T> it) {
        List<T> l = new ArrayList<>();
        it.forEachRemaining(l::add);
        return l;
    }

    public static void main(String[] args) {

        DataStructureBinarySearch ds = new DataStructureBinarySearch();

        DataStructureBinarySearch.Record r1 = new DataStructureBinarySearch.Record(1.0);
        DataStructureBinarySearch.Record r2 = new DataStructureBinarySearch.Record(2.0);
        DataStructureBinarySearch.Record r3 = new DataStructureBinarySearch.Record(3.0);
        DataStructureBinarySearch.Record r4 = new DataStructureBinarySearch.Record(3.1);

        ds.add(r1);
        ds.add(r2);
        ds.add(r3);
        ds.add(r4);

        Iterator<DataStructureBinarySearch.Record> i;

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
