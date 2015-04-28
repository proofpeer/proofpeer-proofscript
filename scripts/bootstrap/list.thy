theory List
extends \root

# Basic list functions

def map [f,xs] =
  for x in xs do
    f x

def
  reverse []        = []
  reverse (x <+ xs) = reverse xs +> x

def foldl [f,xs,b] =
  match xs
    case []      => b
    case x <+ xs => foldl (f,xs,f (b,x))

def foldr [f,xs,b] =
  match xs
    case []      => b
    case x <+ xs => f (x,foldr (f,xs,b))

def every bs =
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

def concat xss =
  for xs in xss do
    for x in xs do
      x

def
  zip [[],_] = []
  zip [_,[]] = []
  zip [x <+ xs, y <+ ys] =
    [x,y] <+ zip (xs,ys)

# Recursively split a value and flatten until failure.
def split [f,x] =
  val ys = f x
  if ys == nil then
    [x]
  else
    for y in ys do
      for s in split (f,y) do
        s

# Recursively split on the left using a binary destructor
def splitLeft [f,x] =
  match f x
    case nil   => [x]
    case [l,r] => splitLeft [f,l] +> r

# And on the right
def splitRight [f,x] =
  match f x
    case nil   => [x]
    case [l,r] => l <+ splitRight [f,r]

# f (f (f ... f x))
def
  iterate [0,_,x] = x
  iterate [n,f,x] = iterate [n-1,f,f x]

assert (foldr (([x,xs] => x <+ xs),[1,2,3],[]) == [1,2,3])