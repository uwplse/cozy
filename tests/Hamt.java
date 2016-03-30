package tests;

import java.util.*;

public class Hamt {

    static final String ALPHA_NUMERIC_STRING = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
    static final int STRING_SIZE = 10;

    static final int N_RUNS = 10000;
    static final long[] SIZES = new long[] {
        /*1L, 10L, 100L, 310L, 1000L, 3100L,
        10000L, 31000L,*/ 100000L/*, 310000L */ };

    public static <T> List<T> list(Iterator<T> it) {
        List<T> l = new ArrayList<>();
        while (it.hasNext()) l.add(it.next());
        return l;
    }

    public static void main(String[] args) {
        // System.out.println("simple testing...");

        // DataStructureHamt ds = new DataStructureHamt();

        // DataStructureHamt.Record r1 = new DataStructureHamt.Record("Ed");
        // DataStructureHamt.Record r2 = new DataStructureHamt.Record("Alice");
        // DataStructureHamt.Record r3 = new DataStructureHamt.Record("Ed");
        // DataStructureHamt.Record r4 = new DataStructureHamt.Record("Kat");

        // ds.add(r1);
        // ds.add(r2);
        // ds.add(r3);
        // ds.add(r4);

        // assert list(ds.q("Ed")).containsAll(Arrays.asList(r1, r3));
        // assert list(ds.q("Alice")).equals(Arrays.asList(r2));

        // ds.remove(r2);
        // assert list(ds.q("Alice")).equals(Collections.emptyList());

        // ds.remove(r3);
        // assert list(ds.q("Ed")).equals(Arrays.asList(r1));

        System.out.println("more testing...");
        System.out.println("warming up...");
        runBenchmark(SIZES, N_RUNS);
        System.out.println("start testing...");
        while (true) {
            long time = runBenchmark(SIZES, N_RUNS);
        }
        // System.out.println("Running time: "+ time);
    }

    public static String buildString(Random rand) {
        StringBuilder builder = new StringBuilder();
        for (int i = 0; i < rand.nextInt(STRING_SIZE) + 1; i++) {
            int index = rand.nextInt(ALPHA_NUMERIC_STRING.length());
            builder.append(ALPHA_NUMERIC_STRING.charAt(index));
        }
        return builder.toString();
    }

    public static long runQueries(Random rand, DataStructureHamt structure, long ntuples, long nqueries) {
        long totalTime = 0;
        for (long x = 0; x < nqueries; ++x) {
            long start = rand.nextLong();
            long end = start + rand.nextInt(10000);

            long startTime = System.nanoTime();
            long count = 0;
            // String s = buildString(rand);
            int s = rand.nextInt(N_RUNS);
            Iterator<DataStructureHamt.Record> it = structure.q(s);
            while (it.hasNext()) {
                it.next();
                ++count;
            }
            totalTime += System.nanoTime() - startTime;
        }
        return totalTime;
    }

    public static long runBenchmark(long[] sizes, long nqueries) {
        long total = 0;
        for (long size : sizes) {
            DataStructureHamt x = new DataStructureHamt();
            System.err.println("benchmarking on size " + size);
            Random rand = new Random(0);
            genData(rand, x, size);
            total += runQueries(rand, x, size, nqueries);
        }
        return total;
    }

    public static void genData(Random rand, DataStructureHamt structure, long ntuples) {
        for (long x = 0; x < ntuples; ++x) {
            // String s = buildString(rand);
            int s = rand.nextInt(N_RUNS);
            structure.add(new DataStructureHamt.Record(s));
        }
    }

}
