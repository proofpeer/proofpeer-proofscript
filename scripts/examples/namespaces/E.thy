theory E 
extends C D

assert x == "B"
failure y
failure z

assert A\x == "A" and A\y == "A" and A\z == "A"
assert B\x == "B" and B\y == "A" and B\z == "A"
assert C\x == "B" and C\y == "C" and C\z == "C"
assert D\x == "B" and D\y == "D" and D\z == "A"

val y = C\y
val z = D\z
assert x == "B" and y == "C" and z == "A"





