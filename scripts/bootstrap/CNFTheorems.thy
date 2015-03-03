theory CNFTheorems
extends Classical

theorem negInvolve: '∀p. (¬(¬p)) = p'
  taut '∀p. (¬(¬p)) = p'

theorem andDeMorgan: '∀p q. (¬(p ∧ q)) = (¬p ∨ ¬q)'
  taut '∀p q. (¬(p ∧ q)) = (¬p ∨ ¬q)'

theorem orDeMorgan: '∀p q. (¬(p ∨ q)) = (¬p ∧ ¬q)'
  taut '∀p q. (¬(p ∨ q)) = (¬p ∧ ¬q)'

theorem notImplies: '∀p q. (¬(p → q)) = (p ∧ ¬q)'
  taut '∀p q. (¬(p → q)) = (p ∧ ¬q)'

theorem impliesCNF: '∀p q. (p → q) = (¬p ∨ q)'
  taut '∀p q. (p → q) = (¬p ∨ q)'

theorem equalCNF: '∀p q. (p = q) = ((p ∨ ¬q) ∧ (¬p ∨ q))'
  taut '∀p q. (p = q) = ((p ∨ ¬q) ∧ (¬p ∨ q))'
