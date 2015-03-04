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

theorem contra: '∀p q. ¬p → p → q'
  taut '∀p q. ¬p → p → q'

theorem existsDeMorgan: '∀P. (¬(∃x. P x)) = (∀x. ¬(P x))'
  let 'P : 𝒰 → ℙ'
  theorem left: '(¬(∃x. P x)) → (∀x. ¬(P x))'
    assume asm:'¬(∃x. P x)'
    let x:'x'
    theorem notPx:
      assume px:'P x'
      theorem pExists:
        val y = fresh "y"
        val asm = let 'y = x'
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
  let 'P : 𝒰 → ℙ'
  val existsDeMorganInst =
    instantiate(existsDeMorgan,'x ↦ ¬(P x)')
  seqConv [randConv (randConv (absConv (rewrConv [gsym negInvolve]))),
           onceTreeConv (rewrConv [gsym existsDeMorganInst]),
           rewrConv [negInvolve]] '¬(∀x. P x)' 0

# As conversions, so that we can exploit higher-order matching.
def
  existsDeMorganConv '(¬(∃x. ‹P› x))' =
    [instantiate (existsDeMorgan, P)]
  existsDeMorganConv _ = []

def
  allDeMorganConv '¬(∀x. ‹P› x)' =
    [instantiate (allDeMorgan, P)]
  allDeMorganConv _ = []

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
        convRule (randConv (subsConv [sym yIsX]),xIsP) 0
      orIntroL (thereIsAP, '(∃x. Q x)')
    theorem case2:
      assume xIsQ:'Q x'
      theorem thereIsAQ:
        val yIsX = let 'y = x'
        convRule (randConv (subsConv [sym yIsX]),xIsQ) 0
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
        (seqConv [rewrConv [orDeMorgan],
                  onceTreeConv existsDeMorganConv],
        (seqConv [existsDeMorganConv, onceTreeConv (rewrConv [orDeMorgan])])),
       onceTreeConv (rewrConv [negInvolve])], disjExistsInst) 0

# As conversions, so that we can exploit higher-order matching.
def
  disjExistsConv '(∃x. ‹P› x) ∨ (∃x. ‹Q› x)' =
    [instantiate (disjExists,P,Q)]
  disjExistsConv _ = []

def
  conjAllConv '(∀x. ‹P› x) ∧ (∀x. ‹Q› x)' =
    [instantiate (conjAll,P,Q)]
  conjAllConv _ = []

theorem trivExists: '∀p. p = (∃x. p)'
  let 'p:ℙ'
  theorem left:'p → (∃x. p)'
    assume p:'p'
    let 'x = ∅'
    p
  theorem right:'(∃x. p) → p'
    assume asm:'∃x. p'
    val p = choose 'x' asm
    p
  equivalence (left,right)

theorem trivAll: '∀p. p = (∀x. p)'
  let 'p:ℙ'
  theorem left:'p → (∀x. p)'
    assume p:'p'
    let 'x'
    p
  theorem right:'(∀x. p) → p'
    assume asm:'∀x. p'
    instantiate (asm,'∅')
  equivalence (left,right)

theorem raiseExistential: '∀P Q. ((∃x. P x) ∧ Q) = (∃x. P x ∧ Q)'
  let 'P : 𝒰 → ℙ'
  let 'Q : ℙ'
  theorem left: '((∃x. P x) ∧ Q) → (∃x. P x ∧ Q)'
    assume asm:'(∃x. P x) ∧ Q'
    val [thereIsAP,q] = conjuncts asm
    val xIsP = choose 'x' thereIsAP
    andIntro (xIsP,q)
  theorem right: '(∃x. P x ∧ Q) → ((∃x. P x) ∧ Q)'
    assume asm:'(∃x. P x ∧ Q)'
    theorem thereIsAP:'∃x. P x'
      val conj = choose 'x' asm
      conjuncts conj 0
    theorem q: 'Q'
      val conj = choose 'x' asm
      conjuncts conj 1
    andIntro (thereIsAP,q)
  equivalence (left,right)

theorem raiseUniversal: '∀P Q. ((∀x. P x) ∨ Q) = (∀x. P x ∨ Q)'
  let 'P : 𝒰 → ℙ'
  let 'Q : ℙ'
  theorem left: '((∀x. P x) ∨ Q) → (∀x. P x ∨ Q)'
    assume asm:'(∀x. P x) ∨ Q'
    let 'x'
    theorem case1:
      assume px:'∀x. P x'
      orIntroL (instantiate (px,'x'), 'Q')
    theorem case2:
      assume q:'Q'
      orIntroR ('P x',q)
    matchmp (orDefEx,asm,case1,case2)
  theorem right: '(∀x. P x ∨ Q) → ((∀x. P x) ∨ Q)'
    assume asm: '∀x. P x ∨ Q'
    theorem ifNotQ:
      assume notq:'¬Q'
      theorem allP:'(∀x. P x)'
        let 'x'
        matchmp (orDefEx,
                 instantiate (asm,'x'),
                 instantiate (trivImp, 'P x'),
                 modusponens (notq,
                              instantiate (contra, 'Q', 'P x')))
      orIntroL (allP,'Q')
    theorem ifQ:
      assume q:'Q'
      orIntroR ('∀x. P x',q)
    matchmp (orDefEx,
             instantiate (excludedMiddle,'Q'),
             ifQ,
             ifNotQ)
  equivalence (left,right)

def
  raiseQuantifiers '(∃x. ‹P› x) ∧ ‹Q›' =
    [instantiate (raiseExistential,P,Q)]
  raiseQuantifiers '(∀x. ‹P› x) ∨ ‹Q›' =
    [instantiate (raiseUniversal,P,Q)]
  raiseQuantifiers ('(∃x. ‹P› x) ∨ ‹Q›' as tm) =
    seqConv (randConv (rewrConv [trivExists]), disjExistsConv) tm
  raiseQuantifiers ('(∀x. ‹P› x) ∧ ‹Q›' as tm) =
    seqConv (randConv (rewrConv [trivAll]), conjAllConv) tm
  raiseQuantifiers ('‹Q› ∧ (∀x. ‹P› x)' as tm) =
    (seqConv [rewrConv [andComm], raiseQuantifiers]) tm
  raiseQuantifiers ('‹Q› ∧ (∃x. ‹P› x)' as tm) =
    (seqConv [rewrConv [andComm], raiseQuantifiers]) tm
  raiseQuantifiers ('‹Q› ∨ (∀x. ‹P› x)' as tm) =
    (seqConv [rewrConv [orComm], raiseQuantifiers]) tm
  raiseQuantifiers ('‹Q› ∨ (∃x. ‹P› x)' as tm) =
    (seqConv [rewrConv [orComm], raiseQuantifiers]) tm
  raiseQuantifiers _ = []

context
  let 'P:𝒰 → ℙ'
  let 'Q:𝒰 → ℙ'
  show conjAllConv '(∀x. P x) ∧ (∀x. Q x)'
  show disjExistsConv '(∃x. P x) ∨ (∃x. Q x)'
  show existsDeMorganConv '¬(∃x. P x)'
  show allDeMorganConv '¬(∀x. P x)'
  show (rhs (normalize (term (raiseQuantifiers '(∃x. P x) ∧ Q = Q' 0))))
  show (rhs (normalize (term (raiseQuantifiers '(∀x. P x) ∨ Q = Q' 0))))
  show (rhs (normalize (term (raiseQuantifiers '(∃x. P x) ∨ Q = Q' 0))))
  show (rhs (normalize (term (raiseQuantifiers '(∀x. P x) ∧ Q = Q' 0))))
  show (rhs (normalize (term (raiseQuantifiers 'Q = Q ∧ (∃x. P x)' 0))))
  show (rhs (normalize (term (raiseQuantifiers 'Q = Q ∨ (∀x. P x)' 0))))
  show (rhs (normalize (term (raiseQuantifiers 'Q = Q ∨ (∃x. P x)' 0))))
  show (rhs (normalize (term (raiseQuantifiers 'Q = Q ∧ (∀x. P x)' 0))))
