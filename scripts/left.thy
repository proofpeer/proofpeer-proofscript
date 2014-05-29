theory left 
extends root

val z ≔ 99

z ≔ 3

val u ≔
  do *
    z ≔ 4
    show z
    val z ≔ 5
    show z

show z
show u
if z > 3 then show z else show -z
if z ≤ 3 then show z else show -z
