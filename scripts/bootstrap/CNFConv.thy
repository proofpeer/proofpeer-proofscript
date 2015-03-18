theory CNFConv
extends CNFTheorems

def binderConv c = randConv (absConv c)

def propBinaryConv c =
  tm =>
    match tm
      case '‹_› ∧ ‹_›' as tm => binaryConv [c,c] tm
      case '‹_› ∨ ‹_›' as tm => binaryConv [c,c] tm
      case                _  => nil

def
  nnf '¬‹_›'      as tm =
    seqConv
      [sumConv (map [rewrConv, [negInvolve,andDeMorgan,orDeMorgan,notImplies]] ++
                               [existsDeMorganConv,allDeMorganConv]),
       nnf] tm
  nnf '‹_› → ‹_›' as tm = seqConv [rewrConv impliesCNF, nnf] tm
  nnf '‹_› = ‹_›' as tm = seqConv [rewrConv equalCNF,   nnf] tm
  nnf                tm = tryConv (sumConv [binderConv nnf, propBinaryConv nnf]) tm


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
  cnfConv '‹_› ∧ ‹_›' as tm = binaryConv (cnfConv,cnfConv) tm
  cnfConv '‹_› ∨ ‹_›' as tm =
    seqConv [binaryConv (cnfConv,cnfConv), disjConv] tm
  cnfConv tm = tryConv (binderConv cnfConv) tm
  disjConv '(‹_› ∧ ‹_›) ∨ ‹_›' as tm =
    seqConv [rewrConv orDistribRight, binaryConv (disjConv, disjConv)] tm
  disjConv '‹_› ∨ (‹_› ∧ ‹_›)' as tm =
    seqConv [rewrConv orDistribLeft, binaryConv (disjConv, disjConv)] tm
  disjConv tm = idConv tm

def
  mkFunTy [ty]        = ty
  mkFunTy (ty <+ tys) = ': ‹ty › → ‹mkFunTy tys›'

def
  mkComb [v]       = v
  mkComb (vs +> v) = '‹mkComb vs› ‹v›'

def
  typeOf '‹_›: ‹a›' = a

def bindersConv c =
  tm =>
    sumConv [c, if iscomb tm and isabs (rand tm)
                then binderConv (bindersConv c)
                else zeroConv tm] tm

val skolem1 =
  def
    skolem1 '∀x: ‹a›. ∃y: ‹b›. ‹p› x y' =
      theorem '(∀x. ∃y. ‹p› x y) = (∃f: ‹a› → ‹b›. ∀x. ‹p› x (f x))'
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
    skolem1 tm = zeroConv tm
  seqConv [skolem1,normalize]

def
  timesConvl [_,c,0] = c
  timesConvl [k,c,n] = timesConvl [k,k c,n-1]

context
  val cthm =
    seqConv [nnf,raiseQuantifiers,cnfConv] '∀p q. (∃x y. p x y) = (∃z. q z)'
  val ctm = rhs (cthm: Term)
  assert
    (ctm == '∀p: 𝒰 → 𝒰 → ℙ. ∀q. ∃x. ∀y z. ∃w u. ((p x w) ∨ (¬q z)) ∧ (q u ∨ ¬(p y z))')
  show ctm
  show (rhs (seqConv [timesConvl
                        [binderConv,
                         seqConv [skolem1,binderConv skolem1],
                         4],
                      timesConvl
                        [binderConv,
                         seqConv [skolem1,binderConv skolem1],
                         3],
                      timesConvl
                        [binderConv,
                         seqConv [skolem1,binderConv skolem1],
                         1],
                       skolem1,
                       binderConv skolem1,
                       timesConvl
                         [binderConv,
                          skolem1,
                          3],
                       timesConvl
                         [binderConv,
                          skolem1,
                          2]
                          ]
                      ctm: Term))
  # val sthm = skolem1 ctm
  # val stm = rhs (sthm: Term)
  # show (rhs (normalize (stm: Term)))
