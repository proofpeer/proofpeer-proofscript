theory Redundancies
extends List Syntax Equal Conversions

theorem orIntroL: '∀ p, q. p → p ∨ q'
  let 'p:ℙ'
  let 'q:ℙ'
  assume p:'p'
  val orElim =
    theorem '∀ z. (p → z) → ((q → z) → z)'
      let 'z:ℙ'
      assume assum:'p → z'
      assume 'q → z'
      modusponens (p,assum)
  modusponens (orElim,sym (apThm (orDef,'p:ℙ','q:ℙ')))
    
theorem orIntroR:'∀ p, q. q → p ∨ q'
  let 'p:ℙ'
  let 'q:ℙ'
  assume q:'q'
  val orElim =
    theorem '∀ z. (p → z) → ((q → z) → z)'
      let 'z:ℙ'
      assume 'p → z'
      assume assum:'q → z'
      modusponens (q,assum)
  modusponens (orElim,sym (apThm (orDef,'p:ℙ','q:ℙ')))

val [conjunct1Thm,conjunct1,conjunct2Thm,conjunct2] =
  val thm1 =
    theorem '∀ p, q. p ∧ q → p'
      let 'p:ℙ'
      let 'q:ℙ'
      assume conj:'p ∧ q'
      eqTrueElim (apThm (modusponens (conj,apThm (andDef,'p:ℙ','q:ℙ')),
                          'x:ℙ ↦ y:ℙ ↦ x'))
  val thm2 =
    theorem '∀ p, q. p ∧ q → q'
        let 'p:ℙ'
        let 'q:ℙ'
        assume conj:'p ∧ q'
        eqTrueElim (apThm (modusponens (conj,apThm (andDef,'p:ℙ','q:ℙ')),
                            'x:ℙ ↦ y:ℙ ↦ y'))
  val conjunct1 = thm =>
    match destconj (term thm)
      case [p,q] => modusponens (thm,instantiate (thm1,p,q))
  val conjunct2 = thm =>
    match destconj (term thm)
      case [p,q] => modusponens (thm,instantiate (thm2,p,q))
  [thm1,conjunct1,thm2,conjunct2]

val [conjThm,conj] =
  val thm =
    theorem '∀ p:ℙ, q:ℙ. p → q → p ∧ q'
      let 'p:ℙ'
      let 'q:ℙ'
      assume p:'p:ℙ'
      assume q:'q:ℙ'
      val conv = treeConv (subsConv [eqTrueIntro p,eqTrueIntro q])
      val thms = convRule [randConv (seqConv [conv,reflConv]),
                           apThm (andDef,'p:ℙ','q:ℙ')]
      val [thm] = thms
      eqTrueElim thm
  [thm,([l,r] => modusponens [r,modusponens [l,instantiate [thm,term l,term r]]])]
      
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
        conj [x,modusponens [x,imp]]
      equivalence [l,r]
    theorem r:'(x ∧ y) = x → (x → y)'
      assume assum:'(x ∧ y) = x'
      theorem 'x → y'
        assume x:'x'
        conjunct2 (modusponens [x,sym assum])
    equivalence [l,r]

show impliesAxRedundant    