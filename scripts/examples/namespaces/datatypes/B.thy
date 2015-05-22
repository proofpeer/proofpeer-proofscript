theory B extends A

def lengthOfList(list : List) : Integer = 
  match list
    case Nil => 0
    case Cons (head, tail) => lengthOfList(tail) + 1

assert lengthOfList Nil == 0
assert lengthOfList (Cons("a", Nil)) == 1
assert lengthOfList (Cons("a", Cons("b", Nil))) == 2
assert A\Nil == Nil


