theory Connectives
extends Conversions Match

theorem trivImp:'∀ p. p → p'
  let 'p:ℙ'
  assume 'p:ℙ'

theorem notFalse:'¬⊥'
  modusponens [instantiate [trivImp,'⊥'],sym (apThm [root\notDef,'⊥'])]

val orIntroL =
  theorem orIntroL:'∀ p q. p → p ∨ q'
    let 'p:ℙ'
    let 'q:ℙ'
    assume p:'p'
    theorem orElim:'∀ z. (p → z) → (q → z) → z'
      let 'z:ℙ'
      assume assum:'p → z'
      assume 'q → z'
      modusponens (p,assum)
    modusponens (orElim,sym (apThm (orDef,'p:ℙ','q:ℙ')))
  [lthm,rterm] => modusponens (lthm,instantiate (orIntroL,term lthm,rterm))

val orIntroR =
  theorem orIntroR:'∀ p, q. q → p ∨ q'
    let 'p:ℙ'
    let 'q:ℙ'
    assume q:'q'
    theorem orElim:'∀ z. (p → z) → (q → z) → z'
      let 'z:ℙ'
      assume 'p → z'
      assume assum:'q → z'
      modusponens (q,assum)
    modusponens (orElim,sym (apThm (orDef,'p:ℙ','q:ℙ')))
  [lterm,rthm] => modusponens (rthm,instantiate (orIntroR,lterm,term rthm))

val conjunct1 =
  theorem conjunct1:'∀ p, q. p ∧ q → p'
    let 'p:ℙ'
    let 'q:ℙ'
    assume conj:'p ∧ q'
    eqTrueElim (apThm (modusponens (conj,apThm (andDef,'p:ℙ','q:ℙ')),
                       'x:ℙ ↦ y:ℙ ↦ x'))
  '‹p› ∧ ‹q›' as thm => modusponens (thm,instantiate (conjunct1,p,q))

val conjunct2 =
  theorem conjunct2:'∀ p, q. p ∧ q → q'
    let 'p:ℙ'
    let 'q:ℙ'
    assume conj:'p ∧ q'
    eqTrueElim (apThm (modusponens (conj,apThm (andDef,'p:ℙ','q:ℙ')),
                       'x:ℙ ↦ y:ℙ ↦ y'))
  '‹p› ∧ ‹q›' as thm => modusponens (thm,instantiate (conjunct2,p,q))

val andIntro =
  theorem andIntro:'∀ p:ℙ, q:ℙ. p → q → p ∧ q'
    let 'p:ℙ'
    let 'q:ℙ'
    assume p:'p:ℙ'
    assume q:'q:ℙ'
    val conv = treeConv (subsConv (eqTrueIntro p,eqTrueIntro q))
    val thms = convRule (randConv (seqConv (conv,reflConv)),
                         apThm (andDef,'p:ℙ','q:ℙ'))
    val [thm] = thms
    eqTrueElim thm
  [l,r] => modusponens (r,modusponens (l,instantiate (andIntro,term l,term r)))

theorem orDef: '∀x y. (x ∨ y) = (∀z. (x → z) → (y → z) → z)'
  let x:'x:ℙ'
  let y:'y:ℙ'
  apThm (orDef,x,y)

theorem notDef: '∀p. (¬p) = (p → ⊥)'
  let p:'p:ℙ'
  apThm (notDef,p)

theorem orAndDistrib1:'∀ p q r. (p ∨ (q ∧ r)) = ((p ∨ q) ∧ (p ∨ r))'
  let 'p:ℙ'
  let 'q:ℙ'
  let 'r:ℙ'

  theorem leftThm:'p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)'
    assume asm:'p ∨ (q ∧ r)'

    theorem case1: 'p → (p ∨ q) ∧ (p ∨ r)'
      assume p:'p:ℙ'
      andIntro (orIntroL (p,'q:ℙ'), orIntroL (p,'r:ℙ'))

    theorem case2: 'q ∧ r → (p ∨ q) ∧ (p ∨ r)'
      assume qr:'q ∧ r'
      andIntro (orIntroR ('p:ℙ',conjunct1 qr), orIntroR ('p:ℙ',conjunct2 qr))

    matchmp (orDef, asm, case1, case2)

  theorem rightThm:'(p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r)'
    assume asm:'(p ∨ q) ∧ (p ∨ r)'

    theorem ifP: 'p → p ∨ (q ∧ r)'
      assume p:'p:ℙ'
      orIntroL (p, '(q ∧ r)')

    theorem ifQ: 'q → p ∨ (q ∧ r)'
      assume q:'q:ℙ'
      theorem ifP: 'p → p ∨ (q ∧ r)'
        assume p:'p:ℙ'
        orIntroL (p,'q ∧ r')
      theorem ifR: 'r → p ∨ (q ∧ r)'
        assume r:'r:ℙ'
        orIntroR ('p:ℙ',andIntro (q,r))
      matchmp (orDef, conjunct2 asm, ifP, ifR)

    matchmp (orDef, conjunct1 asm, ifP, ifQ)

  equivalence (leftThm,rightThm)

theorem orComm: '∀p q. (p ∨ q) = (q ∨ p)'
  theorem lemma: '∀p q. (p ∨ q) → (q ∨ p)'
    let 'p:ℙ'
    let 'q:ℙ'
    assume asm:'p ∨ q'
    theorem ifP:'p → q ∨ p'
      assume p:'p:ℙ'
      orIntroR ('q:ℙ',p)
    theorem ifQ:'q → q ∨ p'
      assume q:'q:ℙ'
      orIntroL (q,'p:ℙ')
    matchmp (orDef, asm, ifP, ifQ)
  let 'p:ℙ'
  let 'q:ℙ'
  theorem left: '(p ∨ q) → (q ∨ p)'
    assume asm:'p ∨ q'
    matchmp (lemma,asm)
  theorem right: '(q ∨ p) → (p ∨ q)'
    assume asm:'q ∨ p'
    matchmp (lemma, asm)
  equivalence (left,right)

theorem orAndDistrib2:'∀p q r. ((p ∧ q) ∨ r) = ((p ∨ r) ∧ (q ∨ r))'
  let 'p:ℙ'
  let 'q:ℙ'
  let 'r:ℙ'
  theorem lemma:'∀p2 q2 r2. ((q2 ∧ r2) ∨ p2) = ((q2 ∨ p2) ∧ (r2 ∨ p2))'
    let 'p2:ℙ'
    let 'q2:ℙ'
    let 'r2:ℙ'
    convRule
      (binaryConv (subsConv [instantiate (orComm,'p2:ℙ','q2 ∧ r2')],
                   binaryConv (subsConv [instantiate (orComm,'p2:ℙ','q2:ℙ')],
                               subsConv [instantiate (orComm,'p2:ℙ','r2:ℙ')])),
              instantiate (orAndDistrib1,'p2:ℙ','q2:ℙ','r2:ℙ')) 0
  instantiate (lemma,'r:ℙ','p:ℙ','q:ℙ')

theorem orRightZero: '∀p. (p ∨ ⊤) = ⊤'
  let 'p:ℙ'
  theorem right: '⊤ → p ∨ ⊤'
    assume '⊤'
    orIntroR ['p:ℙ',truth]
  equivalence (instantiate (topDef,'p ∨ ⊤'),right)

theorem impliesNot: '∀p. (p → ⊥) = (p = ⊥)'
  let 'p:ℙ'
  theorem left: '(p → ⊥) → (p = ⊥)'
    assume asm:'p → ⊥'
    equivalence (asm, instantiate (botDef,'p:ℙ'))
  theorem right: '(p = ⊥) → (p → ⊥)'
    assume asm:'p = ⊥'
    convRule (randConv (rewrConv [asm]),instantiate (trivImp,'p:ℙ')) 0
  equivalence (left,right)

theorem eqFalseWeak: '∀p. (¬p) → (p = ⊥)'
  let 'p:ℙ'
  assume asm:'¬p'
  equivalence (matchmp (notDef,asm), instantiate (botDef,'p:ℙ'))

val eqFalseIntro =
  '¬‹p›' as thm => modusponens (thm,instantiate (eqFalseWeak,p))

theorem eqFalseEq: '∀p. (p = ⊥) = (¬p)'
  let 'p:ℙ'
  theorem left: '(p = ⊥) → ¬p'
    assume asm:'p = ⊥'
    convRule (randConv (rewrConv [sym asm]), notFalse) 0
  equivalence (left,instantiate (eqFalseWeak,'p:ℙ'))

def
  gsym '‹x› = ‹y›' as thm = sym thm
  gsym '∀x. ‹p› x' =
    val [ctx,x,eq] = destabs p
    context <ctx>
      return (gsym eq)