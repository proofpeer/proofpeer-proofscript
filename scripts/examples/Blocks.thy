theory \examples\Blocks extends \root

# do and do*

val x = 
  do*
    1
    2
    3

assert x == [1, 2, 3]

assert (do 7) == 7
assert (do* 7) == [7]

# let us define a map function
def map (f, v) = 
  for x in v do 
    f x

assert map (x => x * x, x) == [1, 4, 9]

# a pyramid
def pyramid n =
  do *
    0 
    for i in 1 to n do
      i
    for i in n-1 downto 1 do
      i
    0

assert pyramid 0 == (0,0)
assert pyramid 1 == (0, 1, 0)
assert pyramid 2 == (0, 1, 2, 1, 0)
assert pyramid 5 == (0, 1, 2, 3, 4, 5, 4, 3, 2, 1, 0) 

# an alternating list of 0s and 1s
def alternate n =
  val zero = true
  val i = 1
  while i <= n do
    if zero then
      0
    else
      1
    zero = not zero
    i = i + 1

assert alternate 0 == []
assert alternate 1 == [0]
assert alternate 9 == [0, 1, 0, 1, 0, 1, 0, 1, 0]
  



