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

# val skolemize =
#   def
#     skolemize ('∀x: ‹a›. ‹p› x' as tm, thm, vs, tys) =
#       val [ctx,x,bod] = destabs '‹p›'
#       val skThm
#       context <ctx>
#         skThm = skolemize ('‹p› ‹x›', thm, vs +> x, tys +> a)
#       skThm
#     skolemize ('∃x: ‹a›. ‹p› x' as tm, thm, vs, tys) =
#       val funTy = mkFunTy (tys +> a)
#       val chosen
#       val ctx =
#         context
#           chosen = choose '‹fresh "f"›: ‹funTy›' thm
#       val f = fresh "f"
#       val skThm
#       context <ctx>
#         val x = mkComb (f <+ vs)
#         skThm = skolemize ('‹p› ‹x›', lift chosen, vs, tys)
#       show skThm
#       skThm
#     skolemize (_, thm, _, _) = thm
#   thm => skolemize (thm: Term,thm,[],[])

def
  skolem1 '∀x: ‹a›. ∃y: ‹b›. ‹p› x y' =
    theorem '(∀x. ∃y. ‹p› x y) = (∃f. ∀x. ‹p› x (f x))'
      theorem left: true
        assume asm:'∀x. ∃y. ‹p› x y'
        choose '‹fresh "f"›' asm
      theorem right: true
        assume asm:'∃f. ∀x. ‹p› x (f x)'
        let x:'‹fresh "x"›: ‹b›'
        choose ch:'‹fresh "f"›' asm
        val '∀x. ‹f› x' = ch
        let ydef:'y = ‹f› ‹x›'
        convRule (randConv (subsConv ydef), instantiate (ch,x))
      equivalence (left,right)


context
  val conved =
    seqConv [nnf,raiseQuantifiers,cnfConv] '∀p q. (∃x y. p x y) = (∃z. q z)'
  val ctm = rhs (conved: Term)
  assert
    (ctm == '∀p q. ∃x. ∀y z. ∃w u. ((p x w) ∨ (¬q z)) ∧ (q u ∨ ¬(p y z))')
