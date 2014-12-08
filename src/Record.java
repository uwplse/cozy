public class Record implements Comparable<Record> {
    private int age;
    private String name;

    public Record(int age, String name)
    {
        this.age = age;
        this.name = name;
    }

    public int getAge()
    {
        return age;
    }

    public String getName()
    {
        return name;
    }

    public boolean equals(Object other)
    {
        return other instanceof Record
           && ((Record)other).age == age
           && ((Record)other).name.equals(name);
    }
    public int compareTo(Record other)
    {
        int ageComp = ((Integer)age).compareTo(other.age);
        if(ageComp == 0)
        {
            return name.compareTo(other.name);
        }
        else
        {
            return ageComp;
        }
    }
    public String toString()
    {
        return "Record(" + age + ", \"" + name + "\")";
    }
}
