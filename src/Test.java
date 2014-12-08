public class Test {
    public static void main(String[] args) {
        DataStructure data = new DataStructure();

        data.add(new Record(1, "a"));
        data.add(new Record(2, "b"));
        data.add(new Record(2, "b"));
        data.add(new Record(3, "c"));
        data.add(new Record(4, "c"));

        System.out.println("Results:");
        for(Record el : data.lookup(2, "c")) {
            System.out.println("Result: " + el);
        }
    }
}
