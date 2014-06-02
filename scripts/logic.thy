theory logic
extends root

val y = 'forall'
show '∃ x. x = ‹y›'

let 'y'
show '∀ q. q = y'
let 'x : 𝒰 → _ : _ → ℙ'
show '∀ q. q = x'
let 'y = x'
let 'x = y'

