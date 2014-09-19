theory Syntax
extends root

# Basic term tools

def
  desteq '‹x› = ‹y›' = [x,y]
  desteq _           = nil

def lhs tm =
  match desteq tm
    case [l,_] => l
    case _     => nil

def rhs tm =
  match desteq tm
    case [_,r] => r
    case _     => nil
