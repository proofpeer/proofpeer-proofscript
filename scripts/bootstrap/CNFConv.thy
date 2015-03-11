theory CNFConv
extends CNFTheorems

def binderConv c = randConv (absConv c)

def propBinaryConv c =
  tm =>
    match tm
      case '‹_› ∧ ‹_›' as tm => binaryConv [c,c] tm
      case '‹_› ∨ ‹_›' as tm => binaryConv [c,c] tm
      case                _  => []

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
    rq '(∃x. ‹P› x) ∧ (∃x. ‹Q› x)' = [instantiate (conjExists,P,Q)]
    rq '(∃x. ‹P› x) ∨ (∃x. ‹Q› x)' = [instantiate (disjExists,P,Q)]
    rq '(∀x. ‹P› x) ∧ (∀x. ‹Q› x)' = [instantiate (conjAll,P,Q)]
    rq '(∀x. ‹P› x) ∨ (∀x. ‹Q› x)' = [instantiate (disjAll,P,Q)]
    rq '(∃x. ‹P› x) ∧ (∀x. ‹Q› x)' = [instantiate (conjExistsAll,P,Q)]
    rq '(∃x. ‹P› x) ∨ (∀x. ‹Q› x)' = [instantiate (disjExistsAll,P,Q)]
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
                        seqConv [rewrConv andComm, rq],
                        seqConv [rewrConv orComm,  rq]]
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

show seqConv [nnf,raiseQuantifiers,cnfConv] '∀p q. (∃x y. p x y) = (∃z. q z)' 0
