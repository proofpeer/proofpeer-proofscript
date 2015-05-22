theory C extends A

def listOfTuple(t : Tuple) : List = 
  val result = Nil
  for x in t do
    result = Cons (x, result)
  reverseList(result)

assert listOfTuple [] == Nil
assert listOfTuple ["a"] == Cons("a", Nil)
assert listOfTuple ["a", "b"] == Cons("a", Cons("b", Nil))
