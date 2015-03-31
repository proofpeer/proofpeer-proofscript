theory CNFConv
extends CNFTheorems

def binderConv c = randConv (absConv c)

def propBinaryConv c =
  tm =>
    match tm
      case '‹_› ∧ ‹_›' as tm => binaryConv [c,c] tm
      case '‹_› ∨ ‹_›' as tm => binaryConv [c,c] tm
      case                _  => nil

def debugConv [name,c] =
  tm =>
    show "Enter"
    show name
    show tm
    val cthm = c tm
    show "Exit"
    show name
    match cthm
      case '‹_› = ‹y›': Theorem => show y
      case _                    => show "failed"
    cthm

def
  nnf '¬⊥'             = notFalseTrue
  nnf '¬⊤'             = notTrueFalse
  nnf '¬‹_›'      as tm =
    tryConv
      (seqConv
        [sumConv (map [rewrConv, [negInvolve,andDeMorgan,orDeMorgan,notImplies]] ++
                                 [existsDeMorganConv,allDeMorganConv]),
         nnf]) tm
  nnf '‹_› → ‹_›' as tm = seqConv [rewrConv impliesCNF, nnf] tm
  nnf '‹_› = ‹_›' as tm = seqConv [rewrConv equalCNF,   nnf] tm
  nnf                tm = sumConv [binderConv nnf, propBinaryConv nnf, idConv] tm

def raiseQuantifiers tm =
  def
    rq '(∃x. ‹P› x) ∧ (∃x. ‹Q› x)' = instantiate (conjExists,P,Q)
    rq '(∃x. ‹P› x) ∨ (∃x. ‹Q› x)' = instantiate (disjExists,P,Q)
    rq '(∀x. ‹P› x) ∧ (∀x. ‹Q› x)' = instantiate (conjAll,P,Q)
    rq '(∀x. ‹P› x) ∨ (∀x. ‹Q› x)' = instantiate (disjAll,P,Q)
    rq '(∃x. ‹P› x) ∧ (∀x. ‹Q› x)' = instantiate (conjExistsAll,P,Q)
    rq '(∃x. ‹P› x) ∨ (∀x. ‹Q› x)' = instantiate (disjExistsAll,P,Q)
    rq '(∃x. ‹P› x) ∧ ‹q›' as tm   = seqConv [randConv trivUnAllConv, rq,
                                              binderConv trivAllConv] tm
    rq '(∃x. ‹P› x) ∨ ‹q›' as tm   = seqConv [randConv trivUnAllConv, rq,
                                     binderConv trivAllConv] tm
    rq '(∀x. ‹P› x) ∧ ‹q›' as tm   = seqConv [randConv trivUnAllConv, rq,
                                              binderConv trivAllConv] tm
    rq '(∀x. ‹P› x) ∨ ‹q›' as tm   = seqConv [randConv trivUnAllConv, rq,
                                              binderConv trivAllConv] tm
    rq tm                          = zeroConv tm
  val rqComm = sumConv [rq,
                        seqConv [rewrConv1 andComm, rq],
                        seqConv [rewrConv1 orComm,  rq]]
  def convl c = sumConv [binderConv (binderConv c), binderConv c]
  sumConv [binderConv raiseQuantifiers,
           seqConv [propBinaryConv raiseQuantifiers, repeatConvl [convl,rqComm]],
           idConv]
          tm

def
  cnf '⊤ ∧ ‹p›'   as tm = seqConv [instantiate (andLeftId, p), cnf] tm
  cnf '‹p› ∧ ⊤'   as tm = seqConv [instantiate (andRightId, p), cnf] tm
  cnf '⊥ ∧ ‹p›'   as tm = instantiate (andLeftZero, p)
  cnf '‹p› ∧ ⊥'   as tm = instantiate (andRightZero, p)
  cnf '‹_› ∧ ‹_›' as tm = binaryConv (cnf,cnf) tm
  cnf '‹_› ∨ ‹_›' as tm =
    seqConv [binaryConv (cnf,cnf), disjConv] tm
  cnf tm = tryConv (binderConv cnf) tm
  disjConv '⊤ ∨ ‹p›' as tm = instantiate (orLeftZero,p)
  disjConv '‹p› ∨ ⊤' as tm = instantiate (orRightZero,p)
  disjConv '⊥ ∨ ‹p›' as tm = seqConv [instantiate (orLeftId,p), disjConv] tm
  disjConv '‹p› ∨ ⊥' as tm = seqConv [instantiate (orRightId,p), disjConv] tm
  disjConv '(‹_› ∧ ‹_›) ∨ ‹_›' as tm =
    seqConv [rewrConv orDistribRight, binaryConv (disjConv, disjConv)] tm
  disjConv '‹_› ∨ (‹_› ∧ ‹_›)' as tm =
    seqConv [rewrConv orDistribLeft, binaryConv (disjConv, disjConv)] tm
  disjConv tm = idConv tm

table skolemThm [a,b] =
  theorem '∀p. (∀x. ∃y. p x y) = (∃f: ‹a› → ‹b›. ∀x. p x (f x))'
    let p:'‹fresh "p"›:‹a› → ‹b› → ℙ'
    theorem left: true
      assume asm:'∀x. ∃y. ‹p› x y'
      choose '‹fresh "f"›' asm
    theorem right: '(∃f:‹a› → ‹b›. ∀x. ‹p› x (f x)) → (∀x. ∃y. ‹p› x y)'
      assume asm:'∃f: ‹a› → ‹b›. ∀x. ‹p› x (f x)'
      let x:'‹fresh "x"›: ‹a›'
      theorem '∃y. ‹p› ‹x› y'
        choose ch:'‹fresh "f"›:‹a› → ‹b›' asm
        val fx = rand (instantiate (ch,x): Term)
        let ydef:'y = ‹fx›'
        convRule (seqConv [randConv (subsConv (gsym ydef)),normalize],
                  instantiate (ch,x))
    equivalence (left,right)

val skolem1 =
  def
    skolem1 '∀x: ‹a›. ∃y: ‹b›. ‹p› x y' = instantiate [skolemThm [a,b],p]
    skolem1 tm = zeroConv tm
  seqConv [skolem1,normalize]

def skolemize tm =
  sumConv [seqConv [skolem1, tryConv skolemize],
           seqConv [binderConv skolemize,
                    tryConv (seqConv [skolem1, skolemize])]] tm

context
  val cthm =
    seqConv [nnf,raiseQuantifiers,cnf,skolemize]
       '∀p q. (∃x y. p x y) = (∃z. q z)'
  val ctm = rhs (cthm: Term)
  assert ctm ==
    '∃f : (𝒰 → 𝒰 → ℙ) → (𝒰 → ℙ) → 𝒰.
       ∃ g : (𝒰 → 𝒰 → ℙ) → (𝒰 → ℙ) → 𝒰 → 𝒰 → 𝒰.
         ∃ h : (𝒰 → 𝒰 → ℙ) → (𝒰 → ℙ) → 𝒰 → 𝒰 → 𝒰.
           ∀p q x y. (p (f p q) (g p q x y) ∨ ¬(q y)) ∧ (q (h p q x y) ∨ ¬ (p x y))'
