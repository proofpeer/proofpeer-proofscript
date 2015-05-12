theory issue63
extends \root

context
  let 'f:𝒰 → 𝒰 → 𝒰 → ℙ'
  val tm = '∀x_1. ∀x_2. ∀x_3. (x_1 ↦ x_2 ↦ f x_1 x_2 x_3) x_2 x_1'
  show normalize tm
  assert tm == '∀x_1. ∀x_2. ∀x_3. f x_2 x_1 x_3'
