theory Redundancies
extends Metis

theorem impliesAxRedundant:'∀ x, y. (x → y) = ((x ∧ y) = x)'
  let 'x:ℙ'
  let 'y:ℙ'
  theorem l:'(x → y) → (x ∧ y) = x'
    assume imp:'x → y'
    theorem l:'x ∧ y → x'
      assume assum:'x ∧ y'
      conjuncts assum 0
    theorem r:'x → x ∧ y'
      assume x:'x'
      andIntro (x,modusponens (x,imp))
    equivalence (l,r)
  theorem r:'(x ∧ y) = x → (x → y)'
    assume assum:'(x ∧ y) = x'
    theorem 'x → y'
      assume x:'x'
      conjuncts (modusponens (x,sym assum)) 1
  equivalence (l,r)

# Useful for certain redudancies.
choose anonymous: 'anonymous: 𝒰'
  let x:'x'
  let 'y = x'
  reflexive 'y'

choose oneDef: 'one:𝒰'
  let one:'one = 𝒫 ∅'
  metisAuto ('∀x. x ∈ one = (x = ∅)', [empty,one,power,subset,ext])

# context
#   let 'one:𝒰'
#   let 'x:𝒰'
#   let 'x_6:𝒰'
#   let 'x_7:𝒰'
#   let 'x_8:𝒰'
#   let 'x_9:𝒰'
#   let 'y_3:𝒰'
    