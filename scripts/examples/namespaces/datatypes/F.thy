theory F extends C D

assert A\Nil == C\Nil <> D\Nil
failure Nil

def f(x : List) = x
def c(x : C\List) = x
assert c A\Nil == C\Nil
failure c D\Nil
failure f A\Nil
failure f D\Nil