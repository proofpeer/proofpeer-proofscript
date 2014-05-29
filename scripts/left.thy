theory left extends root

val z ≔ 99

z ≔ 3

val u ≔
  do 
    z ≔ 4
    show z
    val z ≔ 5
    show z

show z
show u