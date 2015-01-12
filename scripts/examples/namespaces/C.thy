theory C extends B

assert x == "B" and y == "A" and z == "A" 
assert A\x == "A" and B\x == "B"

val y = "C"
val z = "C"

assert x == "B" and y == "C" and z == "C" 