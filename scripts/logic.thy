theory logic
extends root

val y = 'forall'
show '∃ x. x = ‹y›'

let 'y'
show '∀ q. q = y'
let 'x : 𝒰 → _ : _ → ℙ'
show '∀ q. q = x'
let zDef = 'z = x'
show ('z', zDef)
show infinity
choose infinity = 'inf' from infinity
show infinity
show \root\infinity

show "hello \"world\": \u2119 \U0001D4B0"

show "ab" < "ac"
show "ab" > "ac"
show "ab" == "ab"

show match "ab" case "ba" => 1 case "ab" => 2 

val x if x == 2 = 2
show x

val q = ()

context
  let 'z_2'
  let 'z_1'
  assume p = 'z_1 = z_2'
  q = p

show q
show reflexive 'x'
