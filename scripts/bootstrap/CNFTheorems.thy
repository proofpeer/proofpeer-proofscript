theory CNFTheorems
extends Classical

theorem orLeftId: '∀p. (⊥ ∨ p) = p'
  taut '∀p. (⊥ ∨ p) = p'

theorem orLeftZero: '∀p. (⊤ ∨ p) = ⊤'
  taut '∀p. (⊤ ∨ p) = ⊤'

theorem andLeftId: '∀p. (⊤ ∧ p) = p'
  taut '∀p. (⊤ ∧ p) = p'

theorem andLeftZero: '∀p. (⊥ ∧ p) = ⊥'
  taut '∀p. (⊥ ∧ p) = ⊥'

theorem negInvolve: '∀p. (¬(¬p)) = p'
  by taut

theorem andDeMorgan: '∀p q. (¬(p ∧ q)) = (¬p ∨ ¬q)'
  by taut

theorem orDeMorgan: '∀p q. (¬(p ∨ q)) = (¬p ∧ ¬q)'
  by taut

theorem notImplies: '∀p q. (¬(p → q)) = (p ∧ ¬q)'
  by taut

theorem impliesCNF: '∀p q. (p → q) = (¬p ∨ q)'
  by taut

theorem equalCNF: '∀p q. (p = q) = ((p ∨ ¬q) ∧ (¬p ∨ q))'
  by taut

theorem orDistribRight: '∀p q r. ((p ∧ q) ∨ r) = ((p ∨ r) ∧ (q ∨ r))'
  by taut

theorem orDistribLeft: '∀p q r. (p ∨ (q ∧ r)) = ((p ∨ q) ∧ (p ∨ r))'
  by taut

theorem contra: '∀p q. ¬p → p → q'
  by taut

def existsDeMorgan ty =
  theorem '∀P. (¬(∃x:‹ty›. P x)) = (∀x. ¬(P x))'
    val x = fresh "x"
    val P = fresh "P"
    let '‹P› : ‹ty› → ℙ'
    theorem left: '(¬(∃x:‹ty›. ‹P› x)) → (∀x. ¬(‹P› x))'
      assume asm:'¬(∃x:‹ty›. ‹P› x)'
      let '‹x›:‹ty›'
      theorem notPx:
        assume px:'‹P› ‹x›'
        theorem pExists:
          val y = fresh "y"
          val asm = let '‹y› = ‹x›'
          convRule (onceTreeConv (rewrConv1 (sym asm)), px)
        modusponens (pExists, matchmp (notDefEx, asm))
      matchmp (impliesNot, notPx)
    theorem right:
      assume asm:'∀x:‹ty›. ¬(‹P› x)'
      theorem notExP:
        assume exP:'∃x:‹ty›. ‹P› x'
        val px = choose '‹x›:‹ty›' exP
        matchmp (notDefEx, instantiate (asm,'‹x›'), px)
      matchmp (impliesNot, notExP)
    equivalence (left,right)

def allDeMorgan ty =
  theorem '∀P. (¬(∀x:‹ty›. P x)) = (∃x. ¬(P x))'
    val P = fresh "P"
    let '‹P› : ‹ty› → ℙ'
    val existsDeMorganInst =
      instantiate(existsDeMorgan ty,'x ↦ ¬(‹P› x)')
    seqConv [randConv (randConv (absConv (rewrConv1 (gsym negInvolve)))),
             onceTreeConv (rewrConv1 (gsym existsDeMorganInst)),
             rewrConv [negInvolve]] '¬(∀x. ‹P› x)'

# As conversions, so that we can exploit higher-order matching.
def
  existsDeMorganConv '(¬(∃x:‹ty›. ‹P› x))' =
    instantiate (existsDeMorgan ty, P)
  existsDeMorganConv _ = nil

def
  allDeMorganConv '¬(∀x:‹ty›. ‹P› x)' =
    instantiate (allDeMorgan ty, P)
  allDeMorganConv _ = nil

theorem disjExists: '∀P Q. ((∃x. P x) ∨ (∃x. Q x)) = (∃x. P x ∨ Q x)'
  let 'P : 𝒰 → ℙ'
  let 'Q : 𝒰 → ℙ'
  theorem left: '((∃x. P x) ∨ (∃x. Q x)) → (∃x. P x ∨ Q x)'
    assume asm:'(∃x. P x) ∨ (∃x. Q x)'
    theorem case1: '(∃x. P x) → (∃x. P x ∨ Q x)'
      assume asm:'∃x. P x'
      val xIsP = choose 'x' asm
      orIntroL (xIsP, 'Q x')
    theorem case2: '(∃x. Q x) → (∃x. P x ∨ Q x)'
      assume asm:'∃x. Q x'
      val xIsQ = choose 'x' asm
      orIntroR ('P x', xIsQ)
    matchmp (orDefEx,asm,case1,case2)
  theorem right:
    assume asm:'∃x. P x ∨ Q x'
    val xIsPorQ = choose 'x' asm
    theorem case1:
      assume xIsP:'P x'
      theorem thereIsAP:
        val yIsX = let 'y = x'
        convRule (randConv (subsConv (sym yIsX)),xIsP)
      orIntroL (thereIsAP, '(∃x. Q x)')
    theorem case2:
      assume xIsQ:'Q x'
      theorem thereIsAQ:
        val yIsX = let 'y = x'
        convRule (randConv (subsConv (sym yIsX)),xIsQ)
      orIntroR ('∃x. P x', thereIsAQ)
    matchmp (orDefEx,xIsPorQ,case1,case2)
  equivalence (left,right)

theorem conjAll: '∀P Q. ((∀x. P x) ∧ (∀x. Q x)) = (∀x. P x ∧ Q x)'
  let P:'P : 𝒰 → ℙ'
  let Q:'Q : 𝒰 → ℙ'
  val disjExistsInst = combine (reflexive 'p ↦ ¬p',
                                instantiate (disjExists,'x ↦ ¬‹P› x','x ↦ ¬‹Q› x'))
  convRule
    (seqConv
      [binaryConv
         (seqConv [rewrConv1 orDeMorgan,
                   onceTreeConv existsDeMorganConv],
         (seqConv [existsDeMorganConv, onceTreeConv (rewrConv orDeMorgan)])),
       onceTreeConv (rewrConv [negInvolve])], disjExistsInst)

# As conversions, so that we can exploit higher-order matching.
def
  disjExistsConv '(∃x. ‹P› x) ∨ (∃x. ‹Q› x)' =
    instantiate (disjExists,P,Q)
  disjExistsConv _ = nil

theorem trivAll: '∀p. (∀x. p) = p'
  let 'p:ℙ'
  theorem left:'(∀x. p) → p'
    assume asm:'∀x. p'
    instantiate (asm,'∅')
  theorem right:'p → (∀x. p)'
    assume p:'p'
    let 'x'
    p
  equivalence (left,right)

def
  trivAllConv '(∀x. ‹p›)' =
    instantiate (trivAll,p)
  trivAllConv _ = nil

def
  trivUnAllConv '‹p› : ℙ' =
    sym (instantiate (trivAll,p))
  trivUnAllConv _ = nil

# In case we lose the emptyset.
choose anonymous: 'anonymous: 𝒰'
  let x:'x'
  let 'y = x'
  reflexive 'y'

theorem conjExistsAll: '∀P Q. ((∃x. P x) ∧ (∀x. Q x)) = (∃x. ∀y. P x ∧ Q y)'
  let 'P: 𝒰 → ℙ'
  let 'Q: 𝒰 → ℙ'
  theorem left: true
    assume asm:'(∃x. P x) ∧ (∀x. Q x)'
    val xIsP = choose 'x' (conjuncts asm 0)
    let 'y'
    andIntro [xIsP,instantiate (conjuncts asm 1,'y')]
  theorem right: true
    assume asm:'∃x. ∀y. P x ∧ Q y'
    theorem thereIsAP:
      val conj = choose 'x' asm
      conjuncts (instantiate (conj,'anonymous')) 0
    theorem allAreQ:
      val conj = choose 'x' asm
      let 'y'
      conjuncts (instantiate (conj,'y')) 1
    andIntro (thereIsAP, allAreQ)
  equivalence (left,right)

theorem disjExistsAll: '∀P Q. ((∃x. P x) ∨ (∀x. Q x)) = (∃x. ∀y. P x ∨ Q y)'
  let 'P: 𝒰 → ℙ'
  let 'Q: 𝒰 → ℙ'
  theorem left: true
    assume asm:'(∃x. P x) ∨ (∀x. Q x)'
    theorem case1: true
      assume case:'∃x. P x'
      val thereIsAP = choose 'x' case
      let 'y:𝒰'
      orIntroL (thereIsAP, 'Q y')
    theorem case2: true
      assume case:'∀x. Q x'
      let 'x = anonymous'
      let 'y'
      orIntroR ('P x', instantiate (case,'y'))
    matchmp (orDefEx,asm,case1,case2)
  theorem right:
    assume asm:'∃x. ∀y. P x ∨ Q y'
    val porq = choose 'x' asm
    theorem case1:
      assume noP:'∀x. ¬(P x)'
      val noPRule = convRule (onceTreeConv (rewrConv1 (gsym eqFalseSimp)), noP)
      val allQ = convRule (treeConv (rewrConv (noPRule <+ tautRewrites)),porq)
      orIntroR ('∃x. P x',allQ)
    theorem case2:
      assume noNonP:'¬(∀x. ¬(P x))'
      orIntroL (convRule (treeConv (sumConv [allDeMorganConv,
                                             rewrConv1 negInvolve]),
                          noNonP),
                '∀y. Q y')
    matchmp (orDefEx,
             instantiate (excludedMiddle, '∀x. ¬(P x)'),
             case1,
             case2)
  equivalence (left,right)

theorem conjExists: '∀P Q. ((∃x. P x) ∧ (∃x. Q x)) = (∃x y. P x ∧ Q y)'
  let 'P:𝒰 → ℙ'
  let 'Q:𝒰 → ℙ'
  theorem left: true
    assume asm:'(∃x. P x) ∧ (∃x. Q x)'
    val aP = choose 'x' (conjuncts asm 0)
    val aQ = choose 'y' (conjuncts asm 1)
    andIntro [aP,aQ]
  theorem right:
    assume asm:'(∃x y. P x ∧ Q y)'
    val ex   = choose 'x' asm
    val conj = choose 'y' ex
    theorem l: '∃z. P z'
      let zx:'z = x'
      convRule (treeConv (rewrConv1 (gsym zx)), conjuncts conj 0)
    theorem r: '∃z. Q z'
      let zy:'z = y'
      convRule (treeConv (rewrConv1 (gsym zy)), conjuncts conj 1)
    andIntro (l,r)
  equivalence (left,right)

theorem disjAll: '∀P Q. ((∀x. P x) ∨ (∀x. Q x)) = (∀x y. P x ∨ Q y)'
  let p:'P:𝒰 → ℙ'
  let q:'Q:𝒰 → ℙ'
  val neged = instantiate (conjExists,'x ↦ ¬(P x)','x ↦ ¬(Q x)')
  convRule (treeConv (sumConv [existsDeMorganConv,
                               rewrConv [andDeMorgan, negInvolve]]),
            combine (reflexive 'p ↦ ¬p', neged))
