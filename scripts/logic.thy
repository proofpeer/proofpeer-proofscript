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

val q 
show q

context
  let 'z_2'
  let 'z_1'
  assume p = 'z_1 = z_2'
  q = p

show q
show reflexive 'x'
show transitive(zDef, reflexive 'x')

show transitive (reflexive '(y ↦ y) x', reflexive 'x')
show normalize '(y ↦ y) x'

show [,1]
show instantiate (empty, 'y')

show size "hello"


show 2 to 7
show 7 to 2
show 12 downto -8

show "hello" 1
show "hello" [2, 4]

show ["h", "e", "l", "l", "o"] 1
show ["h", "e", "l", "l", "o"] [2, 4]

let 'x_1'
let 'x_2'
let 'x_3'
let 'x_4'
show fresh "x"
let x = '‹fresh "x"›'
show x
show fresh "x"

assume 'x = x'




