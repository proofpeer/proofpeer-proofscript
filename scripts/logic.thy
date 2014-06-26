theory logic
extends root

show context
show context<context>

val y = 'forall'
show '∃ x. x = ‹y›'

let 'y'
show '∀ q. q = y'
let 'x : 𝒰 → _ : _ → ℙ'
show '∀ q. q = x'
let zDef: 'z = x'
show ('z', zDef)
show infinity
val oldinfinity = infinity
choose infinity: 'inf' 
  infinity
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
  assume p: 'z_1 = z_2'
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
let x: '‹fresh "x"›'
show x
show fresh "x"

# This is a comment.
  Comments can span multiple lines,
  no problem!!

def 
  dest t =
    match t
      case '‹p› ∧ ‹q›' => (1, p, q)
      case '∃ X. ‹p› X ∧ ‹q› X' => (2, p, q)
      case '‹p› = ‹q›' => (3, p, q)
      case '∀ x. ‹p› x = ‹q› x' => (4, p, q)
      case _ => nil  

show dest infinity
show dest oldinfinity
show dest '∀ q. q = y'
show dest '∀ q. q = x'

theorem cool: 'x = x' 
  reflexive 'x'

show cool

theorem nice: '∀ p. p → p' 
  let 'p : ℙ'
  assume 'p'

show nice

assume 'x = x'




