theory right 
extends root

val z ≔ 101

if true then
  z ≔ 20

show z

show (3, 1, 7)

val n ≔ 10
val m ≔ 1
while n > 1 do
  m ≔ m * n
  n ≔ n - 1

show m

m ≔ 1

val q ≔
  for i in (1, 2, 3, 4, 5, 6, 7, 8) do
    i
    i * i
    m ≔ m * i
    m
    (i, i * i, m)

show q

match 1
case 2 ⇒ show 2
case 1 ⇒ show 1
case 3 ⇒ show 3

match 4
  case 2 ⇒ show 2
  case 1 ⇒ show 1
  case 3 ⇒ show 3
  case _ ⇒ show 0

val (a, b) ≔ [17, 42]
show a
show b

val a <+ b ≔ [17, 42]
show a
show b

val a +> b ≔ [17, 42]
show a
show b
