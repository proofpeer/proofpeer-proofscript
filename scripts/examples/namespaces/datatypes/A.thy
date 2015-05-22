theory A extends \root

datatype List
  Nil
  Cons (head, tail : List)

def reverseList(list : List) : List = 
  def rev (list, rlist) =
    match list
      case Nil => rlist
      case Cons (head, tail) => rev (tail, Cons (head, rlist))
  rev (list, Nil)

assert reverseList Nil == Nil
assert reverseList (Cons("a", Cons("b", Nil))) == Cons("b", Cons("a", Nil))
failure A\Nil
