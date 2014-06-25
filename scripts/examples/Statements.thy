theory \examples\Statements extends \root


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

def abs x = if x < 0 then -x else x

def gcd (a, b) = 
  a = abs a
  b = abs b
  while b > 0 do
    (a, b) = (b, a mod b)
  a

assert gcd (54, 24) == 6
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

# This implements the map functional
def map (f, v) = for x in v do f x

assert map (x => x * x, [1, 9, 5]) == [1, 81, 25]

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












