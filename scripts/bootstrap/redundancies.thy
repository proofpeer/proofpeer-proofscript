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

theorem '∃one. ∀x. x ∈ one = (x = ∅)'
  let one:'one = 𝒫 ∅'
  assume subset: '∀x y. x ⊂ y = (∀z. z ∈ x → z ∈ y)'
  metisAuto ('∀x. x ∈ one = (x = ∅)', [empty,one,power,subset,ext])