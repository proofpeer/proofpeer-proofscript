theory CustomDatatypes extends \root

#
  deftype 
    Option
      None 
      Some (x : Any)
    List
      Nil
      Cons (head : Any, tail : List)
  sealoff 
    # 

  
