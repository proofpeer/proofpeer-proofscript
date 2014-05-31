theory fun
extends root

val f = x ⇒ x * x

show f
show f 12

def 
  fac 0 = 1
  fac n = n * fac (n - 1)

show fac 10

def
  even 0 = true
  odd 0 = false
  even n = odd (n-1)
  odd n = even (n-1)

def
  first (x, y) = x
  second (x, y) = y

show even 11
show odd 11

val u = (93, 47)
show first u
show second u
show first 10

