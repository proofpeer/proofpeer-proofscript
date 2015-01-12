theory issue27_B extends issue27_A

def g(i) = 
  if i > 0 then  
    i * f(g, i)
  else 
    fail "i is non-positive"

def 
  u 0 = 0
  u 1 = 1

# "failure" swallows the stack trace, replace "failure" by "show" to see the trace
failure u 2

# "failure" swallows the stack trace, replace "failure" by "show" to see the trace
failure g(50)


