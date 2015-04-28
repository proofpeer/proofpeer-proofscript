theory Metis
extends MetisRules

# METIS terms are shadowed on the proofscript side as tuples whose first element is
# the functor, and whose arguments are the (possibly 0) remaining elements. Atomic
# terms are variables, which must *not* be tuples. This is basically the s-expression
# encoding.

def
  functor (f <+ _) = f
  functor _        = fail "Not a term"

def
  args (_ <+ args) = args
  args _           = fail "Not a term"

def isVar term =
  match term
    case term: Tuple => false
    case _           => true

def mkTerm [f,args] = f <+ args

def termVars term =
  if isVar term then
    {term}
  else
    val vs = {}
    for arg in args term do
      vs = vs ++ termVars arg
    vs

def termOfMetis term =
  if isVar term then term
  else mkcombs (functor term <+ map (termOfMetis, args term))

def
  metisOfComb [env,term] =
    match splitLeft [destcomb,term]
      case [x]         =>
        val n = env x
        if n == nil then [x] else n
      case (f <+ args) => f <+ (for arg in args do metisOfComb (env,arg))

def map_term (f, term) =
  if isVar term then f term
  else mkTerm (functor term, for arg in args term do map_term (f, arg))

# METIS literals are a pair whose first element answers whether the literal is
# positive, and the second element is a METIS atom, represented by a METIS term.

def atomOfLiteral [_,atm] = atm

def atomOfMetis atm = termOfMetis atm

def
  literalOfMetis [true,atm]  = atomOfMetis atm
  literalOfMetis [false,atm] = '¬‹atomOfMetis atm›'

val map_atom = map_term

val atomVars = termVars

def map_literal [f,[isPositive,atm]] = [isPositive,map_atom [f,atm]]

def literalVars lit = atomVars (atomOfLiteral lit)

# A clause is a pair whose second element is a theorem thm and whose first element is
# a tuple, associating each of thm's quantifiers in turn with a Metis free-variable
def inClauseFreeAt [freeAt,_]   = freeAt
def clauseThm      [_,thm]      = thm
def mkClause       [freeAt,thm] =
  val [_,xs,_] = stripForall thm
  assert (size xs == size freeAt)
  [freeAt,thm]

def initClause tm =
  val [_,xs,_] = stripForall tm
  [(0 to size xs - 1), tm]

# Generate n fresh constants for each of the given METIS free variables, returning a
# context containing them all, and a map from the METIS free to the new constant.
# For example:
#   freshConsts [7,1,12] == [ctx, { 7 -> z, 1 -> x, 12 -> y }]
# The metalevel quantifiers are ordered according to the input tuple. Thus, on
# lifting p out of this context, we have
#   '∀z x y. ‹p›'
def freshConsts fvs =
  def
    freshs [[],freeAt] =
      return [context,freeAt]
    freshs [fv <+ fvs,freeAt] =
      let x:'‹fresh "x"›'
      return (freshs (fvs,freeAt ++ { fv -> x }))
  context
    return freshs (fvs,{->})

def metisInstantiate [cl,sub:Map] =
  val freeAt = inClauseFreeAt cl
  val clThm  = clauseThm cl
  val minSub = {->}
  sub =
    for [v,tm] if elem (v,freeAt) in sub do
      minSub = minSub ++ {v -> tm}
    minSub
  sub =
    val subDomain = {}
    for [v,_] in sub do subDomain = subDomain ++ {v}
    for fv if not (subDomain fv) in freeAt do sub = sub ++ { fv -> fv }
    sub
  val newFreeAt =
    val fvset = {}
    for [_,tm] in sub do
      for v in termVars tm do
        fvset = fvset ++ {v}
    fvset: Tuple
  val [ctx,varOfMetis] = freshConsts (newFreeAt:Tuple)
  val clThm = clauseThm cl
  context <ctx>
    for v in freeAt do
      val tm = termOfMetis (map_term (varOfMetis, sub v))
      clThm = instantiate (clThm,tm)
    clThm = convRule (nubClauseConv, clThm)
  mkClause (newFreeAt,clThm)

def
  destOr '‹p› ∨ ‹q›' = [p,q]
  destOr (_:Term)    = nil

def
  destNeg '¬‹p›'   = p
  destNeg (p:Term) = p

def atomicInTerm tm =
  val tms = {}
  match splitLeft [destcomb, tm]
    case [v]       => tms = {v}
    case _ <+ args =>
      for arg in args do
        tms = tms ++ atomicInTerm arg
  tms

def atomicInClause cl =
  val tms = {}
  for lit in split [destOr,cl:Term] do
    for (atm:Term) in [lit, destNeg lit] do
      match splitLeft [destcomb, atm]
        case _ <+ args =>
          for arg in args do
            tms = tms ++ atomicInTerm arg
        case _         =>
  tms

def metisResolution [atm,pos,neg] =
  val pos1 = convRule (pullOut atm, pos)
  val neg1 = convRule (pullOut '¬‹atm›', neg)
  val res  =
    val res = matchmp (resolveLeft, pos1, neg1)
    if res <> nil then
      convRule (tryConv (rewrConv orAssoc), res)
    else nil
  if res == nil then
    res = matchmp (resolveTriv1, pos1, neg1)
  if res == nil then
    res = matchmp (resolveTriv2, pos1, neg1)
  if res == nil then
    res = matchmp (finalResolve, pos1, neg1)
  convRule (nubClauseConv, res)

def metisResolve [atm,cl1,cl2] =
  val freeAt1 = inClauseFreeAt cl1
  val freeAt2 = inClauseFreeAt cl2
  val [ctx,varOfMetis1] = freshConsts freeAt1
  val resBody
  val freeAtRes
  context <ctx>
    def
      stripforall2 [[],thm2,freeAtRes,varOfMetis] =
        return [thm2,context,freeAtRes,varOfMetis]
      stripforall2 [v2 <+ vs,thm2,freeAtRes,varOfMetis] =
        val v1 = varOfMetis1 v2
        if v1 == nil then
          let x:'‹fresh "x"›'
          return (stripforall2 (vs,
                                instantiate (thm2,x),
                                freeAtRes +> v2,
                                varOfMetis ++ {v2 -> x}))
        else
          stripforall2 (vs,instantiate [thm2,v1],freeAtRes,varOfMetis)
    val body1       =
      instantiate (clauseThm cl1 <+ (for x in freeAt1 do varOfMetis1 x))
    val [body2,ctx,newFreeAtRes,varOfMetis] =
      stripforall2 (freeAt2,clauseThm cl2,freeAt1,varOfMetis1)
    freeAtRes = newFreeAtRes
    context <ctx>
      resBody = metisResolution
                  (atomOfMetis (map_atom (varOfMetis1, atm)), body1, body2)
      val isAtomic = {}
      for x in atomicInClause resBody do
        isAtomic = isAtomic ++ {x}
      freeAtRes = for fv if isAtomic (varOfMetis fv) in freeAtRes do fv
  mkClause (freeAtRes,resBody)

# METIS clauses are sets of METIS term literals.
def atomOfTerm [env,atm] =
  match metisOfComb (env,atm)
    case compound:Tuple => compound
    case p => [p]

def clauseOfTerm [env,tm] =
  def
    clause '‹p› ∨ ¬‹q›' = clause p ++ {(false, atomOfTerm (env,q))}
    clause '‹p› ∨ ‹q›'  = clause p ++ {(true,  atomOfTerm (env,q))}
    clause '¬‹p›'       = {(false, atomOfTerm (env,p))}
    clause '‹p›'        = {(true,  atomOfTerm (env,p))}
  clause tm

# Take a CNF term and produce the corresponding METIS clauses
def clausesOfCNF tm =
  def
    clauses '‹p› ∧ ‹q›' = clauses p +> withEnvironment ({->},0,q)
    clauses '‹p›'       = [withEnvironment ({->},0,p)]
    withEnvironment [env,n,'∀x. ‹p› x'] =
      val [ctx,x,bod] = destabs p
      val clause
      context <ctx>
        clause = withEnvironment (env ++ { x -> n }, n+1, bod)
      clause
    withEnvironment [env,_,tm] = clauseOfTerm (env,tm)
  clauses tm

theorem refl: '∀x. x = x'
  let 'x'
  reflexive 'x'

val followPath =
  def
    follow [[0],tm,acc]     = [acc,tm]
    follow [i <+ is,tm,acc] =
      val ri = noArgs tm - i - 1
      follow [is,tryRand (iterate [ri,rator,tm]),acc +> ri]
  [is,tm] => follow [is,tm,[]]

def metisEquality [is,lit,rhs] =
  val flipImpliesCNF =
    convRule (binderConv (binderConv (randConv (rewrConv1 orComm))), impliesCNF)
  val [ris,lhs] =
    match lit
      case '¬‹p›' => followPath [is,p]
      case _      => followPath [is,lit]
  def maybeNegConv conv =
    tm =>
      match tm
        case '¬‹p›' => randConv conv tm
        case _      => conv tm
  theorem imp:
    assume asm: lit
    assume eq:'‹lhs› = ‹rhs›'
    def
      equality []          = subsConv eq
      equality (ri <+ ris) =
        iterate
          [ri,
           ratorConv,
           tryConvL [randConv,equality ris]]
    convRule (maybeNegConv (equality ris), asm)
  convRule (seqConv [rewrConv1 impliesCNF,
                     landConv (tryConv (rewrConv1 negInvolve)),
                     randConv (rewrConv1 impliesCNF),
                     rewrConv1 orComm],
            imp)

def interpretCert [axioms,cert] =
  def
    ic ["axiom",cl] =
      assertNotNil (axioms cl)
    ic ["assume",atom] =
      val freeAt = atomVars atom: Tuple
      val [ctx,varOfMetis] = freshConsts freeAt
      val thm
      context <ctx>
        thm = instantiate (excludedMiddle, atomOfMetis (map_atom [varOfMetis,atom]))
      mkClause (freeAt,thm)
    ic ["refl",x] =
      val freeAt  = termVars x: Tuple
      val [ctx,_] = freshConsts freeAt
      val thm
      context <ctx>
        thm = reflexive (termOfMetis x)
      mkClause (freeAt,thm)
    ic [subst:Map, cert] =
      assertNotNil (metisInstantiate [ic cert,subst])
    ic ["resolve", atm, posCert, negCert] =
      val posCl = ic posCert
      val negCl = ic negCert
      assertNotNil (metisResolve [atm,posCl,negCl])
    ic ["irreflexive",cert] =
      val cl = ic cert
      val freeAt = inClauseFreeAt cl
      val [ctx,varOfMetis] = freshConsts freeAt
      val newFreeAt
      val newThm
      context <ctx>
        newThm =
          metisRemoveIrrefl
            (instantiate (clauseThm cl <+ (for x in freeAt do varOfMetis x)))
        val isAtomic = {}
        for x in atomicInClause newThm do
          isAtomic = isAtomic ++ {x}
        newFreeAt = for fv if isAtomic (varOfMetis fv) in freeAt do fv
      mkClause (newFreeAt, newThm)
    ic ["equality",term,literal,path] =
      val newVars = (literalVars literal ++ termVars term):Tuple
      val [ctx,varOfMetis] = freshConsts (newVars:Tuple)
      val thm
      context <ctx>
        val lit = literalOfMetis (map_literal [varOfMetis,literal])
        val tm  = termOfMetis (map_term [varOfMetis,term])
        thm = metisEquality [path,lit,tm]
      mkClause (newVars,thm)
  ic [axioms,cert]

def
  runMetis '∃x. ‹p› x' as thm =
    val f = fresh "f"
    choose chosen: '‹f›'
      thm
    runMetis chosen
  runMetis thm =
    val axioms = {->}
    for ax in conjuncts thm do
      for cl in clausesOfCNF (ax:Term) do
        axioms = axioms ++ { cl -> initClause ax }
    val cert = callmetis (clausesOfCNF (thm:Term))
    if cert == nil then
      nil
    else
      timeit
        interpretCert [axioms,cert]

def letExistentials tm =
  def
    letExists (ctx,'∃x. ‹p› x') =
      val [ctx,x,body] = destabs p
      context <ctx>
        val '‹_›:‹a›' = x
        let x:'‹fresh "x"›:‹a›'
        match letExists (context,body)
          case [ctx,xs,body] =>
            context <ctx>
              return [ctx,x <+ xs,body]
    letExists (ctx,tm) =
      return [ctx,[],tm]
  letExists (context,tm)

val unmetis =
  theorem unmetis1: '∀p q. ¬(p ∧ ¬q) → p → q'
    by taut
  theorem unmetis2: '∀p. ¬(⊤ ∧ ¬p) → ⊤ → p'
    by taut
  thm =>
    val unmetised = matchmp (unmetis1, thm)
    if unmetised == nil then
      matchmp (unmetis2, thm)
    else unmetised

def metis (asms:Tuple) =
  conjecture: Term =>
    val conjAsms       = andIntro asms
    val conjProblem    = '‹conjAsms:Term› ∧ ¬‹conjecture›'
    val conv           =
      seqConv [upConv (sumConv [expandForallIn, expandExistsIn]),
               nnf,prenex,bindersConv cnf,tryConv skolemize]
    val equiv1         =
      timeit
        conv conjProblem
    val skolemNGoal    = rhs (equiv1: Term)
    val [ctx,xs,ngoal] = letExistentials skolemNGoal
    val contr
    context <ctx>
      val equiv2 = distribQuants ngoal
      val dngoal = rhs (equiv2: Term)
      def
        destAnd '‹p› ∧ ‹q›' = [p,q]
        destAnd _           = nil
      theorem refute: '‹dngoal› → ⊥'
        assume asm: dngoal
        clauseThm (runMetis asm)
      val nequiv2 = combine (reflexive 'not', sym equiv2)
      contr = modusponens (convRule ((rewrConv impliesNot), refute), nequiv2)
    def existsDeMorganSym ty = gsym (existsDeMorgan ty)
    def
      existsDeMorganSymConv '(∀x:‹ty›. ¬‹P› x)' =
        instantiate (existsDeMorganSym ty, P)
      existsDeMorganSymConv _ = nil
    def
      upBinderConv tm =
        sumConv [existsDeMorganSymConv,
                 seqConv [binderConv upBinderConv,existsDeMorganSymConv]] tm
    contr = modusponens (convRule (tryConv upBinderConv, contr),
                         combine (reflexive 'not', sym equiv1))
    modusponens (conjAsms, unmetis contr)