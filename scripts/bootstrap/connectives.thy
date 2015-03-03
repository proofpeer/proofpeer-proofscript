theory Connectives
extends Conversions Match

theorem topDef: '∀p. p → ⊤'
  let 'p:ℙ'
  assume 'p:ℙ'
  truth

theorem botDef: '∀p. ⊥ → p'
  let 'p:ℙ'
  assume bot:'⊥'
  instantiate (modusponens (bot, falseDef), 'p:ℙ')

theorem topDefEq: '∀p. (p → ⊤) = ⊤'
  let p:'p:ℙ'
  eqTrueIntro (instantiate (topDef,p))

theorem point: '∀p. (⊤ → p) = p'
  let p:'p:ℙ'
  theorem left:
    assume asm:'⊤ → p'
    modusponens (truth,asm)
  theorem right:
    assume asm:'p:ℙ'
    theorem triv:
      assume '⊤'
      asm
  equivalence (left,right)

theorem botDefEq: '∀p. (⊥ → p) = ⊤'
  let p:'p:ℙ'
  eqTrueIntro (instantiate (botDef,p))

theorem notDefEx: '∀p. (¬p) = (p → ⊥)'
  let p:'p:ℙ'
  apThm (notDef,p)

theorem simpP:'∀p. p = (p = ⊤)'
  let 'p:ℙ'
  theorem left:
    assume p:'p'
    eqTrueIntro p
  theorem right:
    assume pt:'p = ⊤'
    eqTrueElim pt
  equivalence (left,right)

theorem simpNP:'∀p. (¬p) = (p = ⊥)'
  let 'p:ℙ'
  theorem left:
    assume asm:'¬p'
    equivalence (matchmp (notDefEx,asm), instantiate (botDef,'p:ℙ'))
  theorem right:
    assume asm:'p = ⊥'
    eqFalseElim asm
  equivalence (left,right)

theorem simpPNP: '∀p. p → ((¬p) = ⊥)'
  let 'p:ℙ'
  assume p:'p'
  theorem nnp:
    assume np:'¬p'
    matchmp (matchmp (notDefEx,np), p)
  equivalence (nnp, instantiate (botDef,'¬p:ℙ'))

theorem simpNPNP:'∀p. ¬p → ((¬p) = ⊤)'
  let 'p:ℙ'
  assume np:'¬p'
  eqTrueIntro np

theorem notFalseTrue:'(¬⊥) = ⊤'
  eqTrueIntro notFalse

theorem notTrueFalse:'(¬⊤) = ⊥'
  matchmp (simpPNP, truth)

theorem orDefEx: '∀x y. (x ∨ y) = (∀z. (x → z) → (y → z) → z)'
  let x:'x:ℙ'
  let y:'y:ℙ'
  apThm (orDef,x,y)

# ‹p› ↦ ‹p ∨ q›
val orIntroL =
  theorem orIntroL:
    let 'p:ℙ'
    let 'q:ℙ'
    assume p:'p'
    theorem orElim:
      let 'z:ℙ'
      assume assum:'p → z'
      assume 'q → z'
      modusponens (p,assum)
    modusponens (orElim,sym (apThm (\root\orDef,'p:ℙ','q:ℙ')))
  [lthm,rterm] =>
    modusponens (lthm,instantiate (orIntroL,term lthm,rterm))

# ‹q› ↦ ‹p ∨ q›
val orIntroR =
  theorem orIntroR:
    let 'p:ℙ'
    let 'q:ℙ'
    assume q:'q'
    theorem orElim:
      let 'z:ℙ'
      assume 'p → z'
      assume assum:'q → z'
      modusponens (q,assum)
    modusponens (orElim,sym (apThm (\root\orDef,'p:ℙ','q:ℙ')))
  [lterm,rthm] => modusponens (rthm,instantiate (orIntroR,lterm,term rthm))

val conjuncts =
  val conjunct1 =
    theorem conjunct1:
      let 'p:ℙ'
      let 'q:ℙ'
      assume conj:'p ∧ q'
      eqTrueElim (apThm (modusponens (conj,apThm (andDef,'p:ℙ','q:ℙ')),
                         'x:ℙ ↦ y:ℙ ↦ x'))
    thm =>
      match thm
        case '‹p› ∧ ‹q›' as thm => matchmp (conjunct1,thm)
        case _                  => assertThm thm

  val conjunct2 =
    theorem conjunct2:
      let 'p:ℙ'
      let 'q:ℙ'
      assume conj:'p ∧ q'
      eqTrueElim (apThm (modusponens (conj,apThm (andDef,'p:ℙ','q:ℙ')),
                         'x:ℙ ↦ y:ℙ ↦ y'))
    thm =>
      match thm
        case '‹p› ∧ ‹q›' as thm => matchmp (conjunct2,thm)
        case _                  => nil

  def conjs thm =
    val c1 = conjunct1 thm
    if c1 == nil
      then [thm]
      else c1 <+ conjs (conjunct2 thm)
  conjs

# [‹p›,‹q›,...‹r›] ↦ ‹p› ∧ ‹q› ∧ ... ∧ ‹r›
val andIntro =
  theorem andIntro:
    let 'p:ℙ'
    let 'q:ℙ'
    assume p:'p:ℙ'
    assume q:'q:ℙ'
    val conv = treeConv (subsConv (eqTrueIntro p,eqTrueIntro q))
    val thms = convRule (randConv (seqConv (conv,reflConv)),
                         apThm (andDef,'p:ℙ','q:ℙ'))
    val [thm] = thms
    eqTrueElim thm
  def
    loop []        = truth
    loop [p]       = p
    loop (ls +> r) =
      val conj = loop ls
      matchmp (andIntro,conj,r)
  loop

theorem equivalenceGen:'∀f:ℙ → ℙ → ℙ. (∀p q. f p q → f q p) → (∀p q. f p q = f q p)'
  let 'f:ℙ → ℙ → ℙ'
  assume asm:'∀p q. f p q → f q p'
  let p:'p:ℙ'
  let q:'q:ℙ'
  equivalence (instantiate (asm,p,q), instantiate (asm,q,p))

theorem orComm: '∀p q. (p ∨ q) = (q ∨ p)'
  theorem lemma:
    let 'p:ℙ'
    let 'q:ℙ'
    assume asm:'p ∨ q'
    theorem ifP:
      assume p:'p:ℙ'
      orIntroR ('q:ℙ',p)
    theorem ifQ:
      assume q:'q:ℙ'
      orIntroL (q,'p:ℙ')
    matchmp (orDefEx, asm, ifP, ifQ)
  matchmp (equivalenceGen,lemma)

theorem andComm: '∀p q. (p ∧ q) = (q ∧ p)'
  theorem lemma:
    let 'p:ℙ'
    let 'q:ℙ'
    assume pq: 'p ∧ q'
    andIntro (reverse (conjuncts pq))
  matchmp (equivalenceGen,lemma)

theorem orAndDistrib1:'∀ p q r. (p ∨ (q ∧ r)) = ((p ∨ q) ∧ (p ∨ r))'
  let 'p:ℙ'
  let 'q:ℙ'
  let 'r:ℙ'

  theorem leftThm:
    assume asm:'p ∨ (q ∧ r)'

    theorem case1: 'p → (p ∨ q) ∧ (p ∨ r)'
      assume p:'p:ℙ'
      andIntro (orIntroL (p,'q:ℙ'), orIntroL (p,'r:ℙ'))

    theorem case2: 'q ∧ r → (p ∨ q) ∧ (p ∨ r)'
      assume qr:'q ∧ r'
      andIntro (orIntroR ('p:ℙ',conjuncts qr 0), orIntroR ('p:ℙ',conjuncts qr 1))

    matchmp (orDefEx, asm, case1, case2)

  theorem rightThm:
    assume asm:'(p ∨ q) ∧ (p ∨ r)'

    theorem ifP:
      assume p:'p:ℙ'
      orIntroL (p, '(q ∧ r)')

    theorem ifQ:
      assume q:'q:ℙ'
      theorem ifP:
        assume p:'p:ℙ'
        orIntroL (p,'q ∧ r')
      theorem ifR:
        assume r:'r:ℙ'
        orIntroR ('p:ℙ',andIntro (q,r))
      matchmp (orDefEx, conjuncts asm 1, ifP, ifR)

    matchmp (orDefEx, conjuncts asm 0, ifP, ifQ)

  equivalence (leftThm,rightThm)

theorem orAndDistrib2:'∀p q r. ((p ∧ q) ∨ r) = ((p ∨ r) ∧ (q ∨ r))'
  let 'p:ℙ'
  let 'q:ℙ'
  let 'r:ℙ'
  theorem lemma:
    let 'p2:ℙ'
    let 'q2:ℙ'
    let 'r2:ℙ'
    convRule
      (binaryConv (subsConv [instantiate (orComm,'p2:ℙ','q2 ∧ r2')],
                   binaryConv (subsConv [instantiate (orComm,'p2:ℙ','q2:ℙ')],
                               subsConv [instantiate (orComm,'p2:ℙ','r2:ℙ')])),
              instantiate (orAndDistrib1,'p2:ℙ','q2:ℙ','r2:ℙ')) 0
  instantiate (lemma,'r:ℙ','p:ℙ','q:ℙ')

theorem andOrDistrib1:'∀ p q r. (p ∧ (q ∨ r)) = ((p ∧ q) ∨ (p ∧ r))'
  let 'p:ℙ'
  let 'q:ℙ'
  let 'r:ℙ'
  theorem leftThm:
    assume asm:'p ∧ (q ∨ r)'
    val p = conjuncts asm 0
    theorem ifQ:
      assume q:'q'
      orIntroL (andIntro (p,q),'p ∧ r')
    theorem ifR:
      assume r:'r'
      orIntroR ('p ∧ q',andIntro (p,r))
    matchmp (orDefEx, conjuncts asm 1, ifQ, ifR)
  theorem rightThm:
    assume asm:'(p ∧ q) ∨ (p ∧ r)'
    theorem ifPQ:
      assume pq:'p ∧ q'
      andIntro (conjuncts pq 0, orIntroL (conjuncts pq 1, 'r'))
    theorem ifPR:
      assume pr:'p ∧ r'
      andIntro (conjuncts pr 0, orIntroR ('q', conjuncts pr 1))
    matchmp (orDefEx, asm, ifPQ, ifPR)
  equivalence (leftThm, rightThm)

theorem andOrDistrib2:'∀ p q r. ((p ∨ q) ∧ r) = ((p ∧ r) ∨ (q ∧ r))'
  let 'p:ℙ'
  let 'q:ℙ'
  let 'r:ℙ'
  theorem lemma:
    let 'p2:ℙ'
    let 'q2:ℙ'
    let 'r2:ℙ'
    convRule
      (binaryConv (subsConv [instantiate (andComm,'p2:ℙ','q2 ∨ r2')],
                   binaryConv (subsConv [instantiate (andComm,'p2:ℙ','q2:ℙ')],
                               subsConv [instantiate (andComm,'p2:ℙ','r2:ℙ')])),
              instantiate (andOrDistrib1,'p2:ℙ','q2:ℙ','r2:ℙ')) 0
  instantiate (lemma,'r:ℙ','p:ℙ','q:ℙ')

theorem orRightZero: '∀p. (p ∨ ⊤) = ⊤'
  let 'p:ℙ'
  theorem right:
    assume '⊤'
    orIntroR ['p:ℙ',truth]
  equivalence (instantiate (topDef,'p ∨ ⊤'),right)

theorem orLeftZero: '∀p. (⊤ ∨ p) = ⊤'
  convRule (onceTreeConv (rewrConv [orComm]), orRightZero) 0

theorem orRightId: '∀p. (p ∨ ⊥) = p'
  let p:'p:ℙ'
  theorem left:
    assume asm:'p ∨ ⊥'
    matchmp (orDefEx, asm, instantiate (trivImp,p), instantiate (botDef,p))
  theorem right:
    assume p:'p:ℙ'
    orIntroL (p,'⊥')
  equivalence (left, right)

theorem orLeftId: '∀p. (⊥ ∨ p) = p'
  convRule (onceTreeConv (rewrConv [orComm]), orRightId) 0

theorem andRightZero: '∀p. (p ∧ ⊥) = ⊥'
  let p:'p:ℙ'
  theorem left:
    assume asm:'p ∧ ⊥'
    conjuncts asm 1
  theorem right:
    assume asm:'⊥'
    modusponens (asm, instantiate (botDef, 'p ∧ ⊥'))
  equivalence (left,right)

theorem andLeftZero: '∀p. (⊥ ∧ p) = ⊥'
  convRule (onceTreeConv (rewrConv [andComm]), andRightZero) 0

theorem andRightId: '∀p. (p ∧ ⊤) = p'
  let 'p:ℙ'
  theorem left:
    assume asm:'p ∧ ⊤'
    conjuncts asm 0
  theorem right:
    assume p:'p:ℙ'
    andIntro (p,truth)
  equivalence (left,right)

theorem andLeftId: '∀p. (⊤ ∧ p) = p'
  convRule (onceTreeConv (rewrConv [andComm]), andRightId) 0

theorem orIdem: '∀p. (p ∨ p) = p'
  let p:'p:ℙ'
  theorem left:
    assume asm:'p ∨ p'
    val pp = instantiate(trivImp, p)
    matchmp (orDefEx, asm, pp, pp)
  theorem right:
    assume p:'p:ℙ'
    orIntroL (p,'p:ℙ')
  equivalence (left,right)

theorem andIdem: '∀p. (p ∧ p) = p'
  let p:'p:ℙ'
  theorem left:
    assume asm:'p ∧ p'
    conjuncts asm 0
  theorem right:
    assume asm:'p'
    andIntro (asm,asm)
  equivalence (left,right)

theorem andComplement: '∀p. (p ∧ ¬p) = ⊥'
  let p:'p:ℙ'
  theorem left:
    assume asm:'p ∧ ¬p'
    matchmp (matchmp (notDefEx, conjuncts asm 1), conjuncts asm 0)
  theorem right:
    assume asm:'⊥'
    modusponens (asm, instantiate (botDef, 'p ∧ ¬p'))
  equivalence (left,right)

theorem impliesNotEqFalse: '∀p. (p → ⊥) = (p = ⊥)'
  let 'p:ℙ'
  theorem left: '(p → ⊥) → (p = ⊥)'
    assume asm:'p → ⊥'
    equivalence (asm, instantiate (botDef,'p:ℙ'))
  theorem right: '(p = ⊥) → (p → ⊥)'
    assume asm:'p = ⊥'
    convRule (randConv (rewrConv [asm]),instantiate (trivImp,'p:ℙ')) 0
  equivalence (left,right)

def
  eqFalseIntro '¬‹p›' as thm = modusponens (thm,instantiate (simpNP,p))
  eqFalseIntro thm           = assertThm thm

theorem eqTrueEq: '∀p. (p = ⊤) = p'
  gsym simpP

theorem eqFalseEq: '∀p. (p = ⊥) = (¬p)'
  gsym simpNP

theorem impliesNot: '∀p. (p → ⊥) = (¬p)'
  convRule (treeConv (rewrConv [eqFalseEq]), impliesNotEqFalse) 0

theorem andDeMorgan: '∀p q. (¬(p ∨ q)) = (¬p ∧ ¬q)'
  let 'p:ℙ'
  let 'q:ℙ'
  theorem left:
    assume asm:'¬(p ∨ q)'
    theorem notP:
      assume p:'p:ℙ'
      matchmp (andComplement, andIntro (orIntroL (p, 'q:ℙ'), asm))
    theorem notQ:
      assume q:'q:ℙ'
      matchmp (andComplement, andIntro (orIntroR ('p:ℙ',q),asm))
    andIntro (matchmp (impliesNot,notP), matchmp (impliesNot,notQ))
  theorem right:
    assume asm:'¬p ∧ ¬q'
    theorem notpq:
      assume pq: 'p ∨ q'
      theorem notP:
        assume p:'p:ℙ'
        matchmp (andComplement,andIntro (p, conjuncts asm 0))
      theorem notQ:
        assume q:'q:ℙ'
        matchmp (andComplement,andIntro (q, conjuncts asm 1))
      matchmp (orDefEx, pq, notP, notQ)
    matchmp (impliesNot, notpq)
  equivalence (left,right)

theorem curry:'∀p q r. (p ∧ q → r) → p → q → r'
  let 'p:ℙ'
  let 'q:ℙ'
  let 'r:ℙ'
  assume imp:'p ∧ q → r'
  assume p:'p'
  assume q:'q'
  modusponens (andIntro (p,q), imp)
