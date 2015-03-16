theory Statements extends \root


# do
  -------------------------------

assert (do 42) == 42 <> [42] == (do* 42)

do
  # we are surrounding the following statements with do
    to avoid polluting the namespace of the theory with the
    definition of x and y, which are rather arbitrary names
  val x = 10
  val y = 
    do*
      x
      x
       + 1
      x + 2
  assert y == [10, 11, 12]


# if
  -------------------------------

assert (if true then 1 else 2) == 1
assert (if false then 1 else 2) == 2
failure (if nil then 1 else 2)


# match
  -------------------------------

val wordOf = x => 
  match x
    case 0 => "none"
    case 1 => "one"
    case 2 => "two"
    case z if z > 0 => "many"

assert wordOf 0 == "none" and wordOf 1 == "one" and wordOf 2 == "two"
assert wordOf 5 == "many"
failure wordOf (-1)


# while
  -------------------------------

def gcd (a, b) = 
  if a < 0 then a = -a
  if b < 0 then b = -b
  while b > 0 do
    (a, b) = (b, a mod b)
  a

assert gcd (54, 24) == 6
assert gcd (-54, -24) == 6
assert gcd (54, 25) == 1


# for
  -------------------------------

# This function sums up all the elements of a vector which are non-negative integers
def sum v =
  val s = 0
  for x if x >= 0 in v do
    s = s + x
  s

assert sum (1, 2, 3, 4, 5, -10, "hello", 7) == 22
assert sum () == 0

# the function also works for sets
assert sum {1, 2, 3, 4, 5, -10, "hello", 7} == 22
assert sum {} == sum {->} == 0
assert sum {4, 3, 3} == 7

# This implements the map functional for vectors
def map (f, v) = for x in v do f x

assert map (x => x * x, [1, 9, 5]) == [1, 81, 25]

# You can apply map also to sets, but you still get a vector
assert map (x => x * x, {1, 9, 5}) == [1, 81, 25]

# Here is how you can swap keys and values in a Map
def swap (m : Map) : Map = 
  val result = {->}
  for (k, v) in m do
    result = result ++ {v -> k}
  result

assert swap {2 -> 3, 3 -> 5, 5 -> 7, 7 -> 11} == {3 -> 2, 5 -> 3, 7 -> 5, 11 -> 7}

# And this implements the fold functional
def fold (f, x, v) =
  for y in v do
    x = f (x, y)
  x

assert fold ((x, y) => x + y, 8, [1, 2, 3, 4, 5, 7]) == 30

# Finally, foldmap
def foldmap (f, x, v) =
  for y in v do
    x = f (x, y)
    x

assert foldmap ((x, y) => x + y, 8, [1, 2, 3, 4, 5, 7]) == [9, 11, 14, 18, 23, 30]


# val, def and rebinding
  -------------------------------

do
  val x = 3
  val y if x == 3 =
    x + x
  assert y == 6

do
  val x = 3
  val y if x == 3 =
    val x = 2
    x + x
  assert y == 4

failure
  val x = 3
  val y if x == 3 =
    x = 2
    x + x

def 
  fac 0 = 1
  fac 1 = 1
  fac n = n * fac (n - 1)

assert fac 10 == 3628800

def 
  even 0 = true
  odd 0 = false
  even n if n > 0 = odd (n - 1)
  odd n if n > 0 = even (n - 1)
  even n if n < 0 = odd (n + 1)
  odd n if n < 0 = even (n + 1)

assert even 24 == even (-24) == true
assert odd 24 == odd (-24) == false
failure even "24"
failure odd "24"

even = "even"

assert even == "even" and odd 24 == false

# return
  -------------------------------

# look up element in association list
def lookup (x, v) = 
  for (key, value) in v do 
    if x == key then return value
  return

val proofpeers = [("Steven", "Obua"), ("Jacques", "Fleuriot"), 
  ("Phil", "Scott"), ("David", "Aspinall")]

assert lookup ("Jacques", proofpeers) == "Fleuriot"
assert lookup ("Marilyn", proofpeers) == nil

# fail
  -------------------------------

# This function computes the integer square root of an integer if it
  actually exists. Otherwise it fails.
def sqrt x =
  if x < 0 then fail
  for i in 0 to x do
    if i * i == x then return i
  fail

assert sqrt 1024 == 32
failure sqrt (-1)
assert sqrt 9 == 3
assert sqrt 0 == 0
assert sqrt 1 == 1
assert sqrt 4 == 2
failure sqrt 10







