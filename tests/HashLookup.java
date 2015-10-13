package tests;

import java.util.*;

public class HashLookup {

    public static <T> List<T> list(Iterator<T> it) {
        List<T> l = new ArrayList<>();
        it.forEachRemaining(l::add);
        return l;
    }

    public static void main(String[] args) {

        DataStructureHashLookup ds = new DataStructureHashLookup();

        DataStructureHashLookup.Record r1 = new DataStructureHashLookup.Record("Ed");
        DataStructureHashLookup.Record r2 = new DataStructureHashLookup.Record("Alice");
        DataStructureHashLookup.Record r3 = new DataStructureHashLookup.Record("Ed");
        DataStructureHashLookup.Record r4 = new DataStructureHashLookup.Record("Kat");

        ds.add(r1);
        ds.add(r2);
        ds.add(r3);
        ds.add(r4);

        assert list(ds.q("Ed")).containsAll(Arrays.asList(r1, r3));
        assert list(ds.q("Alice")).equals(Arrays.asList(r2));

        ds.remove(r2);
        assert list(ds.q("Alice")).equals(Collections.emptyList());
        assert list(ds.q("Ed")).containsAll(Arrays.asList(r1, r3));

        ds.remove(r3);
        assert list(ds.q("Ed")).equals(Arrays.asList(r1));

    }

}
