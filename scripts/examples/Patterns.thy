theory \examples\Patterns extends \root

def 
  f 0 = true
  f [1, 2, 7] = true
  f "hello" = true
  f false = true
  f _ = false

assert f 0
assert not f 1
assert f [1, 2, 7]
assert f "hello"
assert not f "hello world"
assert f false
assert not f true

def 
  sum [] = 0
  sum x <+ xs = x + sum xs

def
  fibPrefix [] = true
  fibPrefix [0] = true
  fibPrefix [0, 1] = true
  fibPrefix xs +> x +> y +> z = 
    fibPrefix (xs +> x +> y) and z == x + y

assert fibPrefix []
assert fibPrefix [0]
assert fibPrefix [0, 1]
assert fibPrefix [0, 1, 1]
assert fibPrefix [0, 1, 1, 2]
assert fibPrefix [0, 1, 1, 2, 3]
assert fibPrefix [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]
assert not fibPrefix [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 56, 89]

def 
  g [] = true
  g xs +> x if g xs = 
    size xs == x

assert g []
assert g [0]
assert g [0, 1]
assert g [0, 1, 2]
assert g [0, 1, 2, 3]
assert not g [0, 1, 2, 3, 5]

def 
  brackets [] = true
  brackets "(" <+ s +> ")" = brackets s
  brackets _ = false

assert brackets []
assert brackets ["(", ")"]
assert brackets ["(","(",")",")"]
assert brackets ["(", "(", "(", "(", ")", ")", ")", ")"]
assert not brackets ["(", "(", ")"]


