theory ifl extends \root

def fib n =
  val a = 0
  val b = 1
  val i = 0 
  while i < n do
    val c=a+b 
    b=a
    a=c
    i=i+1
  return a

show [fib 0, fib 1, fib 2, fib 3, fib 4, fib 5, fib 6]

def f a =
  val b = 
     if a > 0 then 
        a = 2
        5
     else 
        a = 3
        7
  a + b

show f 2
show f (-2)

def g a =
  val b = 5
  b = 
     if a > 0 then 
        a = 2
        5
     else 
        a = 3
        7
  a + b

show g 2
show g (-2)
  