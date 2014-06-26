theory \B extends \A

assert x == "A" and y == "A" and z == "A" 

val x = "B"

assert x == "B" and \A\x == "A" 
