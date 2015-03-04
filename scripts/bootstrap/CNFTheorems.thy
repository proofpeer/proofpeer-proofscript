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

# Quantifier rules as conversions, since we need to be "polymorphic" in P and Q.
def
  existsDeMorganConv '(¬(∃x. ‹P› x))' =
    theorem thm: '(¬(∃x. ‹P› x)) = (∀x. ¬(‹P› x))'
      val x = fresh "x"
      theorem left: '(¬(∃x. ‹P› x)) → (∀x. ¬(‹P› x))'
        assume asm:'¬(∃x. ‹P› x)'
        let x:'‹x›'
        theorem notPx:
          assume px:'‹P› ‹x›'
          theorem pExists:
            val y = fresh "y"
            val asm = let '‹y› = ‹x›'
            convRule (onceTreeConv (rewrConv [sym asm]), px) 0
          modusponens (pExists, matchmp (notDefEx, asm))
        matchmp (impliesNot, notPx)
      theorem right:
        assume asm:'∀x. ¬(‹P› x)'
        theorem notExP:
          assume exP:'∃x. ‹P› x'
          val px = choose '‹x›' exP
          matchmp (notDefEx, instantiate (asm,'‹x›'), px)
        matchmp (impliesNot, notExP)
      equivalence (left,right)
    [thm]
  existsDeMorganConv _ = []

def
  allDeMorganConv '¬(∀x. ‹P› x)' =
    theorem thm: '(¬(∀x. ‹P› x)) = (∃x. ¬(‹P› x))'
      theorem left: '(¬(∀x. ‹P› x)) → (∃x. ¬(‹P› x))'
        assume asm:'¬(∀x. ‹P› x)'
        theorem notnotExists:
          assume notExNotP:'¬(∃x. ¬(‹P› x))'
          val contra =
            convRule (onceTreeConv (rewrConv [negInvolve]),
                      modusponens (notExNotP,
                                   existsDeMorganConv '¬(∃x. ¬‹P› x)' 0)) 0
          modusponens (contra, matchmp (notDefEx, asm))
        convRule (treeConv (rewrConv [negInvolve,impliesNot]), notnotExists) 0
      theorem right: '(∃x. ¬(‹P› x)) → ¬(∀x. ‹P› x)'
        assume asm:'∃x. ¬(‹P› x)'
        theorem notAll:
          assume allPx:'∀x. ‹P› x'
          val y = fresh "y"
          val notPy = choose '‹y›' asm
          matchmp (notDefEx, notPy, instantiate (allPx, '‹y›'))
        matchmp (impliesNot, notAll)
      equivalence (left,right)
    [thm]
  allDeMorganConv _ = []

def
  conjAllConv '(∀x. ‹P› x) ∧ (∀x. ‹Q› x)' =
    theorem thm: '((∀x. ‹P› x) ∧ (∀x. ‹Q› x)) = (∀x. ‹P› x ∧ ‹Q› x)'
      val x = fresh "x"
      theorem left: '((∀x. ‹P› x) ∧ (∀x. ‹Q› x)) → (∀x. ‹P› x ∧ ‹Q› x)'
        assume asm:'(∀x. ‹P› x) ∧ (∀x. ‹Q› x)'
        val [asm1,asm2] = conjuncts asm
        let '‹x›'
        andIntro (instantiate (asm1,'‹x›'),instantiate (asm2,'‹x›'))
      theorem right:
        assume asm:'(∀x. ‹P› x ∧ ‹Q› x)'
        theorem allp:
          let '‹x›'
          conjuncts (instantiate (asm,'‹x›')) 0
        theorem allq: '∀x. ‹Q› x'
          let '‹x›'
          conjuncts (instantiate (asm,'‹x›')) 1
        andIntro (allp,allq)
      equivalence (left,right)
    [thm]
  conjAllConv _ = []


def
  disjExistsConv '(∃x. ‹P› x) ∨ (∃x. ‹Q› x)' =
    theorem thm: '((∃x. ‹P› x) ∨ (∃x. ‹Q› x)) = (∃x. ‹P› x ∨ ‹Q› x)'
      val x = fresh "x"
      val y = fresh "y"
      theorem left: '((∃x. ‹P› x) ∨ (∃x. ‹Q› x)) → (∃x. ‹P› x ∨ ‹Q› x)'
        assume asm:'(∃x. ‹P› x) ∨ (∃x. ‹Q› x)'
        theorem case1: '(∃x. ‹P› x) → (∃x. ‹P› x ∨ ‹Q› x)'
          assume asm:'∃x. ‹P› x'
          val xIsP = choose '‹x›' asm
          orIntroL (xIsP, '‹Q› x')
        theorem case2: '(∃x. ‹Q› x) → (∃x. ‹P› x ∨ ‹Q› x)'
          assume asm:'∃x. ‹Q› x'
          val xIsQ = choose '‹x›' asm
          orIntroR ('‹P› ‹x›', xIsQ)
        matchmp (orDefEx,asm,case1,case2)
      theorem right:
        assume asm:'∃x. ‹P› x ∨ ‹Q› x'
        val xIsPorQ = choose '‹x›' asm
        theorem case1:
          assume xIsP:'‹P› ‹x›'
          theorem thereIsAP:
            val yIsX = let '‹y› = ‹x›'
            convRule (randConv (subsConv [sym yIsX]),xIsP) 0
          orIntroL (thereIsAP, '(∃x. ‹Q› x)')
        theorem case2:
          assume xIsQ:'‹Q› ‹x›'
          theorem thereIsAQ:
            val yIsX = let '‹y› = ‹x›'
            convRule (randConv (subsConv [sym yIsX]),xIsQ) 0
          orIntroR ('∃x. ‹P› x', thereIsAQ)
        matchmp (orDefEx,xIsPorQ,case1,case2)
      equivalence (left,right)
    [thm]
  disjExistsConv _ = []

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

def
  raiseQuantifier '(∃x. ‹P› x) ∧ ‹Q›' =
    theorem thm: '((∃x. ‹P› x) ∧ ‹Q›) = (∃x. ‹P› x ∧ ‹Q›)'
      val x = fresh "x"
      theorem left: '((∃x. ‹P› x) ∧ ‹Q›) → (∃x. ‹P› x ∧ ‹Q›)'
        assume asm:'(∃x. ‹P› x) ∧ ‹Q›'
        val [thereIsAP,q] = conjuncts asm
        val xIsP = choose '‹x›' thereIsAP
        andIntro (xIsP,q)
      theorem right: '(∃x. ‹P› x ∧ ‹Q›) → ((∃x. ‹P› x) ∧ ‹Q›)'
        assume asm:'(∃x. ‹P› x ∧ ‹Q›)'
        theorem thereIsAP:'∃x. ‹P› x'
          val conj = choose '‹x›' asm
          conjuncts conj 0
        theorem q: '‹Q›'
          val conj = choose '‹x›' asm
          conjuncts conj 1
        andIntro (thereIsAP,q)
      equivalence (left,right)
    [thm]
  raiseQuantifier '(∀x. ‹P› x) ∨ ‹Q›' =
    theorem thm: '((∀x. ‹P› x) ∨ ‹Q›) = (∀x. ‹P› x ∨ ‹Q›)'
      val x = fresh "x"
      theorem left: '((∀x. ‹P› x) ∨ ‹Q›) → (∀x. ‹P› x ∨ ‹Q›)'
        assume asm:'(∀x. ‹P› x) ∨ ‹Q›'
        let '‹x›'
        theorem case1:
          assume px:'∀x. ‹P› x'
          orIntroL (instantiate (px,'‹x›'), '‹Q›')
        theorem case2:
          assume q:'‹Q›'
          orIntroR ('‹P› ‹x›',q)
        matchmp (orDefEx,asm,case1,case2)
      theorem right: '(∀x. ‹P› x ∨ ‹Q›) → ((∀x. ‹P› x) ∨ ‹Q›)'
        assume asm: '∀x. ‹P› x ∨ ‹Q›'
        theorem ifNotQ:
          assume notq:'¬‹Q›'
          theorem allP:'(∀x. ‹P› x)'
            let '‹x›'
            matchmp (orDefEx,
                     instantiate (asm,'‹x›'),
                     instantiate (trivImp, '‹P› ‹x›'),
                     modusponens (notq,
                                  instantiate (contra, '‹Q›', '‹P› ‹x›')))
          orIntroL (allP,'‹Q›')
        theorem ifQ:
          assume q:'‹Q›'
          orIntroR ('∀x. ‹P› ‹x›',q)
        matchmp (orDefEx,
                 instantiate (excludedMiddle,'‹Q›'),
                 ifQ,
                 ifNotQ)
      equivalence (left,right)
    [thm]
  raiseQuantifier ('(∃x. ‹P› x) ∨ ‹Q›' as tm) =
    seqConv (randConv (rewrConv [trivExists]), disjExistsConv) tm
  raiseQuantifier ('(∀x. ‹P› x) ∧ ‹Q›' as tm) =
    seqConv (randConv (rewrConv [trivAll]), conjAllConv) tm
  raiseQuantifier _ = []

context
  let 'P:𝒰 → ℙ'
  let 'Q:𝒰 → ℙ'
  show conjAllConv '(∀x. P x) ∧ (∀x. Q x)'
  show disjExistsConv '(∃x. P x) ∨ (∃x. Q x)'
  show existsDeMorganConv '¬(∃x. P x)'
  show allDeMorganConv '¬(∀x. P x)'
  show (rhs (normalize (term (raiseQuantifier '(∃x. P x) ∧ Q = Q' 0))))
  show (rhs (normalize (term (raiseQuantifier '(∀x. P x) ∨ Q = Q' 0))))
  show (rhs (normalize (term (raiseQuantifier '(∃x. P x) ∨ Q = Q' 0))))
  show (rhs (normalize (term (raiseQuantifier '(∀x. P x) ∧ Q = Q' 0))))
