theory List
extends root

# Basic list functions

def foldl (f,xs,b) =
  match xs
    case []      => b
    case x <+ xs => foldl (f,xs,f b x)

val every = bs =>
  for b in bs do
    if not b then return false
  return true

def
  elem [_,[]]      = false
  elem [x,y <+ ys] = x == y or elem (x,ys)

def
  assoc [_,[]] = nil
  assoc [k,(theKey,v) <+ kvs] =
    if k == theKey then
      [v]
    else
      assoc (k,kvs)