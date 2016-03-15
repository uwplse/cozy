static final String ALPHA_NUMERIC_STRING = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
static final int STRING_SIZE = 10;

static final int N_RUNS = 10000;
static final int DISTINCT_QUERIES = 10;
static final int DISTINCT_FRAGMENTS = 10;
static final long[] SIZES = new long[] {
    1L, 10L, 100L, 310L, 1000L, 3100L,
    10000L, 31000L, 100000L, 310000L };

// set to true to force a different kind of plan to be generated
static final boolean START_IS_USELESS = true;

void genData(Random rand, DataStructure structure, long ntuples) {
    for (long x = 0; x < ntuples; ++x) {
        // String s = buildString(rand);
        int s = rand.nextInt(N_RUNS);
        structure.add(new DataStructure.Record(s));
    }
}

String buildString(Random rand) {
    StringBuilder builder = new StringBuilder();
    for (int i = 0; i < rand.nextInt(STRING_SIZE) + 1; i++) {
        int index = rand.nextInt(ALPHA_NUMERIC_STRING.length());
        builder.append(ALPHA_NUMERIC_STRING.charAt(index));
    }
    return builder.toString();
}

long runQueries(Random rand, DataStructure structure, long ntuples, long nqueries) {
    long totalTime = 0;
    for (long x = 0; x < nqueries; ++x) {
        long start = rand.nextLong();
        long end = start + rand.nextInt(10000);

        long startTime = System.nanoTime();
        long count = 0;
        // String s = buildString(rand);
        int s = rand.nextInt(N_RUNS);
        Iterator<DataStructure.Record> it = structure.q(s);
        while (it.hasNext()) {
            it.next();
            ++count;
        }
        totalTime += System.nanoTime() - startTime;
    }
    return totalTime;
}

long runBenchmark(long[] sizes, long nqueries) {
    long total = 0;
    for (long size : sizes) {
        DataStructure x = new DataStructure();
        System.err.println("benchmarking on size " + size);
        Random rand = new Random(0);
        genData(rand, x, size);
        total += runQueries(rand, x, size, nqueries);
    }
    return total;
}

void run() {
    System.err.println("warming up...");
    runBenchmark(SIZES, N_RUNS);
    System.err.println("running...");
    System.out.println(runBenchmark(SIZES, N_RUNS));
}
