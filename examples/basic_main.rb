require_relative "basic.rb"

m = Basic.new([1, 2, 3])
def cb(e)
  puts e
end
puts "before"
m.elems(method(:cb))

m.add(4)
m.remove(1)

puts "after"

m.elems(method(:cb))

