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
