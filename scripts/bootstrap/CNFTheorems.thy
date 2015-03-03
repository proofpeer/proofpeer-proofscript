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

theorem existsDeMorgan: '∀P. (¬(∃x. P x)) = (∀x. ¬(P x))'
  let 'P:𝒰 → ℙ'
  theorem left: '(¬(∃x. P x)) → (∀x. ¬(P x))'
    assume asm:'¬(∃x. P x)'
    let 'x:𝒰'
    theorem notPx:
      assume px:'P x'
      theorem pExists:
        let asm:'y = x'
        convRule (onceTreeConv (rewrConv [sym asm]), px) 0
      modusponens (pExists, matchmp (notDefEx, asm))
    matchmp (impliesNot, notPx)
  theorem right:
    assume asm:'∀x. ¬(P x)'
    theorem notExP:
      assume exP:'∃x. P x'
      val px = choose 'x' exP
      matchmp (notDefEx, instantiate (asm,'x'), px)
    matchmp (impliesNot, notExP)
  equivalence (left,right)

theorem allDeMorgan: '∀P. (¬(∀x. P x)) = (∃x. ¬(P x))'
  let 'P:𝒰 → ℙ'
  theorem left: '(¬(∀x. P x)) → (∃x. ¬(P x))'
    assume asm:'¬(∀x. P x)'
    theorem notnotExists:
      assume notExNotP:'¬(∃x. ¬(P x))'
      val contra =
        convRule (onceTreeConv (rewrConv [negInvolve]),
                  modusponens (notExNotP,
                               instantiate (existsDeMorgan,'x ↦ ¬(P x)'))) 0
      modusponens (contra, matchmp (notDefEx, asm))
    convRule (treeConv (rewrConv [negInvolve,impliesNot]), notnotExists) 0
  theorem right: '(∃x. ¬(P x)) → ¬(∀x. P x)'
    assume asm:'∃x. ¬(P x)'
    theorem notAll:
      assume allPx:'∀x. P x'
      val notPy = choose 'y' asm
      matchmp (notDefEx, notPy, instantiate (allPx, 'y'))
    matchmp (impliesNot, notAll)
  equivalence (left,right)