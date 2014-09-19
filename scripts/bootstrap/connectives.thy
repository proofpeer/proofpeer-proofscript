theory Connectives
extends Conversions

val orIntroL =
  theorem thm: '∀ p, q. p → p ∨ q'
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
  [lthm,rterm] => modusponens (lthm,instantiate (thm,term lthm,rterm))

val orIntroR =
  theorem thm:'∀ p, q. q → p ∨ q'
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
  [lterm,rthm] => modusponens (rthm,instantiate (thm,lterm,term rthm))

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
    val '‹p› ∧ ‹q›' = term thm
    modusponens (thm,instantiate (thm1,p,q))
  val conjunct2 = thm =>
    val '‹p› ∧ ‹q›' = term thm
    modusponens (thm,instantiate (thm2,p,q))
  [thm1,conjunct1,thm2,conjunct2]

val [conjThm,andIntro] =
  val thm =
    theorem '∀ p:ℙ, q:ℙ. p → q → p ∧ q'
      let 'p:ℙ'
      let 'q:ℙ'
      assume p:'p:ℙ'
      assume q:'q:ℙ'
      val conv = treeConv (subsConv (eqTrueIntro p,eqTrueIntro q))
      val thms = convRule (randConv (seqConv (conv,reflConv)),
                           apThm (andDef,'p:ℙ','q:ℙ'))
      val [thm] = thms
      eqTrueElim thm
  [thm,([l,r] => modusponens (r,modusponens (l,instantiate (thm,term l,term r))))]

theorem orAndDistrib:'∀ p q r. (p ∧ (q ∨ r)) = ((p ∧ q) ∨ (p ∧ r))'
  let 'p:ℙ'
  let 'q:ℙ'
  let 'r:ℙ'
  val left = 'p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r)'
  theorem leftThm:left
    assume conj:'p ∧ (q ∨ r)'

    val '‹_› → ‹goal›' = left
    val p = conjunct1 conj

    theorem qgoal:'q → ‹goal›'
      assume q:'q:ℙ'
      orIntroL (andIntro (p,q),'p ∧ r')
    theorem rgoal:'r → ‹goal›'
      assume r:'r:ℙ'
      orIntroR ('p ∧ q',andIntro (p,r))
    val unfoldOr = modusponens (conjunct2 conj,apThm (orDef,'q:ℙ','r:ℙ'),goal)
    modusponens (rgoal,modusponens (qgoal,instantiate (unfoldOr,goal)))
  show left
  val right = '(p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r)'
  theorem rightThm:right
    assume disj:'(p ∧ q) ∨ (p ∧ r)'
    val '‹_› → ‹goal›' = right
    val '‹disjl› ∨ ‹disjr›' = term disj
    val unfoldOr = modusponens (disj,apThm (orDef,disjl,disjr))

    theorem l:'p ∧ q → p ∧ (q ∨ r)'
      assume pq:'p ∧ q'
      andIntro (conjunct1 pq,orIntroL (conjunct2 pq,'r:ℙ'))

    theorem r:'p ∧ r → p ∧ (q ∨ r)'
      assume pr:'p ∧ r'
      andIntro (conjunct1 pr,orIntroR ('q:ℙ',conjunct2 pr))

    modusponens (r,modusponens (l,instantiate (unfoldOr,goal)))
  equivalence (leftThm,rightThm)
