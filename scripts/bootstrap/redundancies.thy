theory Redundancies
extends Connectives

val impliesAxRedundant =
  theorem '∀ x, y. (x → y) = ((x ∧ y) = x)'
    let 'x:ℙ'
    let 'y:ℙ'
    theorem l:'(x → y) → (x ∧ y) = x'
      assume imp:'x → y'
      theorem l:'x ∧ y → x'
        assume assum:'x ∧ y'
        conjunct1 assum
      theorem r:'x → x ∧ y'
        assume x:'x'
        andIntro (x,modusponens (x,imp))
      equivalence (l,r)
    theorem r:'(x ∧ y) = x → (x → y)'
      assume assum:'(x ∧ y) = x'
      theorem 'x → y'
        assume x:'x'
        conjunct2 (modusponens (x,sym assum))
    equivalence (l,r)
