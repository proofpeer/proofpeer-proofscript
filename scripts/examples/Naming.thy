theory \examples\Naming extends \root

val square = x => x * x
val square_of_7 = square 7
show square_of_7

val n = 0
show n
n = 1
show n
n = 2
show n

val q = 5
val times_q = x => q * x
val u = times_q 7
q = 6
val v = times_q 7
assert 35 == u == v <> q * 7 == 42

val define_later
assert define_later == nil

val init
if v < 10 then
  init = v * 10
else
  init = v * 12
show init
