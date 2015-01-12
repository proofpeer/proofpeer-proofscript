theory D extends B

assert x == "B" and y == "A" and z == "A" 
assert A\x == "A" and B\x == "B"

val y = "D"

assert x == "B" and y == "D" and z == "A" 