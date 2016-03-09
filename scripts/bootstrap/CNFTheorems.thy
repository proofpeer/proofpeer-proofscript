theory CNFTheorems
extends Classical

theorem orLeftId: '∀p. (⊥ ∨ p) = p'
  by taut

theorem orLeftZero: '∀p. (⊤ ∨ p) = ⊤'
  by taut

theorem andLeftId: '∀p. (⊤ ∧ p) = p'
  by taut

theorem andLeftZero: '∀p. (⊥ ∧ p) = ⊥'
  by taut

theorem negInvolve: '∀p. (¬(¬p)) = p'
  by taut

theorem andDeMorgan: '∀p q. (¬(p ∧ q)) = (¬p ∨ ¬q)'
  by taut

theorem orDeMorgan: '∀p q. (¬(p ∨ q)) = (¬p ∧ ¬q)'
  by taut

theorem notImplies: '∀p q. (¬(p → q)) = (p ∧ ¬q)'
  by taut

theorem notEquiv: '∀p q. (¬(p = q)) = ((p ∨ q) ∧ (¬p ∨ ¬q))'
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

def
  expandForallIn 'forallin ‹x› ‹p›' =
    instantiate (forallin, '‹x›', '‹p›')
  expandForallIn _ = nil

def
  expandExistsIn 'existsin ‹x› ‹p›' =
    instantiate (existsin, '‹x›', '‹p›')
  expandExistsIn _ = nil

table<context> existsDeMorgan ty =
  theorem '∀p. (¬(∃x:‹ty›. p x)) = (∀x. ¬(p x))'
    val x = fresh "x"
    val p = fresh "p"
    let '‹p› : ‹ty› → ℙ'
    theorem left: '(¬(∃x:‹ty›. ‹p› x)) → (∀x. ¬(‹p› x))'
      assume asm:'¬(∃x:‹ty›. ‹p› x)'
      let '‹x›:‹ty›'
      theorem notPx:
        assume px:'‹p› ‹x›'
        theorem pExists:
          val y = fresh "y"
          val asm = let '‹y› = ‹x›'
          convRule (onceTreeConv (rewrConv1 (sym asm)), px)
        modusponens (pExists, matchmp (notDefEx, asm))
      matchmp (impliesNot, notPx)
    theorem right:
      assume asm:'∀x:‹ty›. ¬(‹p› x)'
      theorem notExP:
        assume exP:'∃x:‹ty›. ‹p› x'
        val px = choose '‹x›:‹ty›' exP
        matchmp (notDefEx, instantiate (asm,'‹x›'), px)
      matchmp (impliesNot, notExP)
    equivalence (left,right)

table<context> allDeMorgan ty =
  theorem '∀P. (¬(∀x:‹ty›. P x)) = (∃x. ¬(P x))'
    val p = fresh "p"
    let '‹p› : ‹ty› → ℙ'
    val existsDeMorganInst =
      instantiate(existsDeMorgan ty,'x ↦ ¬(‹p› x)')
    seqConv [randConv (randConv (absConv (rewrConv1 (gsym negInvolve)))),
             onceTreeConv (rewrConv1 (gsym existsDeMorganInst)),
             rewrConv [negInvolve]] '¬(∀x. ‹p› x)'

# As conversions, so that we can exploit higher-order matching.
def
  existsDeMorganConv '(¬(∃x:‹ty›. ‹p› x))' =
    instantiate (existsDeMorgan ty, p)
  existsDeMorganConv _ = nil

def
  allDeMorganConv '¬(∀x:‹ty›. ‹p› x)' =
    instantiate (allDeMorgan ty, p)
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
  let p:'P : 𝒰 → ℙ'
  let q:'Q : 𝒰 → ℙ'
  val disjExistsInst = combine (reflexive 'p ↦ ¬p',
                                instantiate (disjExists,'x ↦ ¬‹p› x','x ↦ ¬‹q› x'))
  convRule
    (seqConv
      [binaryConv
         (seqConv [rewrConv1 orDeMorgan,
                   onceTreeConv existsDeMorganConv],
         (seqConv [existsDeMorganConv, onceTreeConv (rewrConv orDeMorgan)])),
       onceTreeConv (rewrConv [negInvolve])], disjExistsInst)

# As conversions, so that we can exploit higher-order matching.
def
  disjExistsConv '(∃x. ‹p› x) ∨ (∃x. ‹q› x)' =
    instantiate (disjExists,p,q)
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
  theorem left: nil!
    assume asm:'(∃x. P x) ∧ (∀x. Q x)'
    val xIsP = choose 'x' (conjuncts asm 0)
    let 'y'
    andIntro [xIsP,instantiate (conjuncts asm 1,'y')]
  theorem right: nil!
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
  theorem left: nil!
    assume asm:'(∃x. P x) ∨ (∀x. Q x)'
    theorem case1: nil!
      assume case:'∃x. P x'
      val thereIsAP = choose 'x' case
      let 'y:𝒰'
      orIntroL (thereIsAP, 'Q y')
    theorem case2: nil!
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
  theorem left: nil!
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
