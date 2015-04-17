theory CNFConv
extends CNFTheorems

def binderConv c = randConv (absConv c)

def bindersConv c =
  tm =>
    match tm
      case '∀x. ‹p› x' as tm => binderConv (bindersConv c) tm
      case '∃x. ‹p› x' as tm => binderConv (bindersConv c) tm
      case tm                => c tm

# Apply a conversion to both sides of a conjunction or disjunction.
def propBinaryConv c =
  tm =>
    match tm
      case '‹_› ∧ ‹_›' as tm => binaryConv [c,c] tm
      case '‹_› ∨ ‹_›' as tm => binaryConv [c,c] tm
      case                _  => nil

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
  nnf '(‹_›:ℙ) = ‹_›' as tm = seqConv [rewrConv equalCNF,   nnf] tm
  nnf                tm = sumConv [binderConv nnf, propBinaryConv nnf, idConv] tm

# Conversion from nnf to prenex form.
def prenex tm =
  def
    rq '(∃x. ‹P› x) ∧ (∃x. ‹Q› x)' = instantiate (conjExists,P,Q)
    rq '(∃x. ‹P› x) ∨ (∃x. ‹Q› x)' = instantiate (disjExists,P,Q)
    rq '(∀x. ‹P› x) ∧ (∀x. ‹Q› x)' = instantiate (conjAll,P,Q)
    rq '(∀x. ‹P› x) ∨ (∀x. ‹Q› x)' = instantiate (disjAll,P,Q)
    rq '(∃x. ‹P› x) ∧ (∀x. ‹Q› x)' = instantiate (conjExistsAll,P,Q)
    rq '(∃x. ‹P› x) ∨ (∀x. ‹Q› x)' = instantiate (disjExistsAll,P,Q)
    rq '(∃x. ‹P› x) ∧ ‹q›'         =
      convRule (binaryConv (randConv trivAllConv, binderConv trivAllConv),
                instantiate (conjExistsAll,P,'x ↦ ‹q›'))
    rq '(∃x. ‹P› x) ∨ ‹q›'         =
      convRule (binaryConv (randConv trivAllConv, binderConv trivAllConv),
                instantiate (disjExistsAll,P,'x ↦ ‹q›'))
    rq '(∀x. ‹P› x) ∧ ‹q›'         =
      convRule (landConv (randConv trivAllConv),
                instantiate (conjAll, P, 'x ↦ ‹q›'))
    rq '(∀x. ‹P› x) ∨ ‹q›'         =
      convRule (binaryConv (randConv trivAllConv, binderConv trivAllConv),
                instantiate (disjAll, P, 'x ↦ ‹q›'))
    rq tm                          = zeroConv tm

  val rqComm = sumConv [rq,
                        seqConv [rewrConv1 andComm, rq],
                        seqConv [rewrConv1 orComm,  rq]]

  def repeatRq tm =
    seqConv [rqComm, tryConv (binderConv (bindersConv repeatRq))] tm

  def prenex1 tm =
    tryConv (seqConv [propBinaryConv prenex, tryConv (debugConv ("rq",repeatRq))]) tm

  sumConv [bindersConv prenex1, prenex1] tm

theorem andAssoc: '∀p q r. (p ∧ (q ∧ r)) = (p ∧ r ∧ q)'
  by taut

theorem orAssoc: '∀p q r. (p ∨ (q ∨ r)) = (p ∨ r ∨ q)'
  by taut

# Conversion from an nnf matrix to cnf.
val cnf =
  val andConv =
    seqConv
      [sumConv ((for thm in [andLeftId, andRightId, andLeftZero, andRightZero] do
                   rewrConv1 thm) +> idConv),
       tryConv (debugConv ("rewriting and-assoc",rewrConv andAssoc))]
  val orConv =
    seqConv
      [sumConv ((for thm in [orLeftId, orRightId, orLeftZero, orRightZero] do
                   rewrConv1 thm) +> idConv),
       tryConv rewrConv orAssoc]
  def
    cnfConv '‹_› ∧ ‹_›' as tm =
      seqConv [binaryConv (cnfConv,cnfConv), andConv] tm
    cnfConv '‹_› ∨ ‹_›' as tm =
      seqConv [binaryConv (cnfConv,cnfConv), disjConv, tryConv orConv] tm
    cnfConv tm = idConv tm
    disjConv '(‹_› ∧ ‹_›) ∨ ‹_›' as tm =
      seqConv [rewrConv orDistribRight,
               binaryConv (disjConvOrConv, disjConvOrConv),
               tryConv andConv] tm
    disjConv '‹_› ∨ (‹_› ∧ ‹_›)' as tm =
      seqConv [rewrConv orDistribLeft,
               binaryConv (disjConvOrConv, disjConvOrConv),
               tryConv andConv] tm
    disjConv tm = idConv tm
    disjConvOrConv tm = seqConv [disjConv, tryConv orConv] tm
  repeatConvl [binderConv, cnfConv]

val flipConjAll = gsym conjAll

# Distribute quantifiers over their conjunctive matrix, dropping ones that
# become redundant.
def distribQuants tm =
  def
    repeat tm = seqConv [binaryConv [tryConv trivAllConv, tryConv trivAllConv],
                         landConv db1] tm

    db1 '(∀x. ‹P› x ∧ ‹Q› x)' as tm =
      val flippedConjAll = instantiate (flipConjAll, P, Q)
      flippedConjAll = modusponens (flippedConjAll, normalize (flippedConjAll:Term))
      convRule (randConv repeat, flippedConjAll)
    db1 p = idConv p

  def db tm = tryConv (seqConv [binderConv db, db1]) tm

  db tm

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
        let ydef:'‹fresh "y"› = ‹fx›'
        convRule (seqConv [randConv (subsConv (gsym ydef)),normalize],
                  instantiate (ch,x))
    equivalence (left,right)

val skolem1 =
  def
    skolem1 '∀x: ‹a›. ∃y: ‹b›. ‹p› x y' = instantiate [skolemThm [a,b],p]
    skolem1 tm = zeroConv tm
  seqConv [skolem1,normalize]

def
  skolemize '∀x:‹_›. ‹P› x' as tm =
    seqConv [binderConv skolemize,
             tryConv (seqConvl [binderConv, skolem1])] tm
  skolemize tm = tryConv (binderConv skolemize) tm

context
  val cthm =
    seqConv [nnf,prenex,cnf,skolemize]
       '∀p q. (∃x y. p x y) = (∃z. q z)'
  val ctm = rhs (cthm: Term)
  assert ctm ==
    '∃f : (𝒰 → 𝒰 → ℙ) → (𝒰 → ℙ) → 𝒰.
       ∃ g : (𝒰 → 𝒰 → ℙ) → (𝒰 → ℙ) → 𝒰 → 𝒰 → 𝒰.
         ∃ h : (𝒰 → 𝒰 → ℙ) → (𝒰 → ℙ) → 𝒰 → 𝒰 → 𝒰.
           ∀p q x y. (p (f p q) (g p q x y) ∨ ¬(q y)) ∧ (q (h p q x y) ∨ ¬ (p x y))'

context
  let 'p : (𝒰 → 𝒰 → ℙ)'
  let 'q : (𝒰 → 𝒰 → ℙ)'
  let 'f : (𝒰 → 𝒰)'
  val cthm = distribQuants '∀x y z w. p x (f y) ∧ q y z ∧ p (f x) (f (f w))': Term
  val ctm = rhs (cthm: Term)
  assert ctm ==
    '(∀ x y. p x (f y)) ∧ (∀x y. q x y) ∧ (∀x y. (p (f x)) (f (f y)))'
