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

def vars term =
  if isVar term then
    {term}
  else
    val vs = {}
    for arg in args term do
      vs = vs ++ vars arg
    vs

def combOfMetis term =
  if isVar term then term
  else mkcombs (functor term,map (combOfMetis, args term))

def
  metisOfComb term =
    match splitLeft [destcomb,term]
      case [x]         => x
      case (f <+ args) => f <+ (for arg in args do metisOfComb arg)

def map_term (f, term) =
  if isVar term then f term
  else mkTerm (functor term, for arg in args term do map_term (f, arg))

# METIS literals are a pair whose first element answers whether the literal is
# positive, and the second element is a METIS atom, represented by a METIS term.

def
  isPositive [isPos,_] = isPos
  isPositive _         = fail "Not a literal"

def
  atom [_,atm] = atm
  atom _       = fail "Not an atom"

def atomOfMetis atm = combOfMetis atm

def
  literalOfMetis [true,atm]  = atomOfMetis atm
  literalOfMetis [false,atm] = '¬‹atomOfMetis atm›'

# A clause is a pair whose first element is a tuple, associating each quantifier in
# turn with a Metis free-variable [fvs,tm]
def inClauseFreeAt [freeAt,_]   = freeAt
def clauseThm      [_,thm]      = thm
def mkClause       [freeAt,thm] = [freeAt,thm]

def initClause tm =
  val [_,xs,_] = stripForall tm
  [(0 to size xs - 1), tm]

# Generate n fresh variables, returning a context containing them all, and a map from
# each to the index of the implicit quantifier, outermost first. For example, given
#   freshVars 3 == [ctx, { x -> 1, y -> 2, z -> 3 }]
# lifting a theorem p out of ctx will produce ∀x y z. ‹p›
def freshVars (fvs:Tuple) =
  def
    freshs [[],freeAt,ctx] =
      [ctx,freeAt]
    freshs [fv <+ fvs,freeAt,ctx] =
      ctx =
        context <ctx>
          let x:'‹fresh "x"›'
          freeAt = freeAt ++ { fv -> x }
      freshs (fvs,freeAt,ctx)
  val ctx = context
  freshs (fvs,{->},ctx)

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
      for v in vars tm do
        fvset = fvset ++ {v}
    fvset: Tuple
  val [ctx,freeIndex] = freshVars newFreeAt
  context <ctx>
    for v in freeAt do
      val tm = combOfMetis (map_term (freeIndex cl, sub v))
      clThm  = instantiate (clauseThm cl,tm)
    clThm = convRule (nubClauseConv, clThm)
  mkClause [newFreeAt,clThm]

def
  destOr '‹p› ∨ ‹q›' = [p,q]
  destOr (_:Term)    = nil

def
  destNeg '¬‹p›'   = p
  destNeg (p:Term) = p

def termFrees tm =
  match splitLeft [destcomb, tm]
    case _ <+ args => map [termFrees, args]
    case v         => [v]

def bodyFrees cl =
  for lit in split [destOr,cl:Term] do
    for (atm:Term) in [lit, destNeg lit] do
      match splitLeft [destcomb, atm]
        case _ <+ args => map [termFrees, args]
        case _         => []

def metisResolve [atm,cl1,cl2] =
  val freeAt1 = inClauseFreeAt cl1
  val freeAt2 = inClauseFreeAt cl2
  val [ctx,freeIndex1] = freshVars freeAt1
  val freeAtRes = freeAt1
  val resBody
  context <ctx>
    def
      stripforall2 [[],thm2,ctx] = [thm2,ctx]
      stripforall2 [v2 <+ vs,thm2,ctx] =
        val vi1 = freeIndex1 v2
        if vi1 == nil then
          val newThm2
          val newCtx =
            context <ctx>
              let x:'‹fresh "x"›'
              freeAtRes = freeAtRes +> x
              newThm2 = stripforall2 [vs,instantiate (thm2,x)]
          stripforall2 [vs,newThm2,newCtx]
        else
          val v1 = freeIndex1 vi1
          stripforall2 [vs,instantiate [thm2,v1],ctx]
    val body1       = instantiate (clauseThm cl1 <+ freeAt1)
    val [body2,ctx] = stripforall2 [freeAt2,clauseThm cl2,ctx]
    context <ctx>
      resBody         = metisResolution [atomOfMetis atm, body1, body2]
      val resFrees    = bodyFrees resBody
      freeAtRes       = for fv if elem [fv,resFrees] in freeAtRes do fv
  mkClause [freeAtRes,resBody]

# METIS clauses are sets of METIS term literals.
def atomOfTerm atm =
  match metisOfComb atm
    case compound:Tuple => compound
    case p => [p]

def
  clauseOfTerm '‹p› ∨ ¬‹q›' = clauseOfTerm p ++ {(false, atomOfTerm q)}
  clauseOfTerm '‹p› ∨ ‹q›'  = clauseOfTerm p ++ {(true,  atomOfTerm q)}
  clauseOfTerm '¬‹p›'       = {(false, atomOfTerm p)}
  clauseOfTerm '‹p›'        = {(true,  atomOfTerm p)}

# Take a CNF term and produce the corresponding METIS clauses
def clausesOfCNF tm =
  match tm
    case '‹p› ∧ ‹q›' => clausesOfCNF p +> clauseOfTerm q
    case '‹p›'       => [ clauseOfTerm p ]

def interpretCert [axioms,cert] =
  def
    ic ["axiom",cl] =
      axioms cl
    ic [subst:Map, cert] =
      metisInstantiate [ic cert,subst]
    ic ["resolve", atm, posCert, negCert] =
      val posCl = ic posCert
      val negCl = ic negCert
      metisResolve [atm,posCl,negCl]
  ic [axioms,cert]

def
  metis '∃x. ‹p› x' as thm =
    val f = fresh "f"
    choose chosen: '‹f›'
      thm
    metis chosen
  metis thm =
    val axioms = {->}
    for ax in conjuncts thm do
      axioms = axioms ++ { clauseOfTerm ax -> initClause ax }
    val cert = callmetis (clausesOfCNF thm)
    interpretCert [axioms,cert]

val unmetis =
  theorem unmetis1: '∀p q. (p ∧ ¬q → ⊥) → p → q'
    taut '∀p q. (p ∧ ¬q → ⊥) → p → q'
  theorem unmetis2: '∀p. (¬p → ⊥) → ⊤ → p'
    taut '∀p. (¬p → ⊥) → ⊤ → p'
  thm =>
    val unmetised = matchmp (unmetis1, thm)
    if unmetised == nil then
      matchmp (unmetis2, thm)
    else unmetised

def metisAuto [asms:Tuple,conjecture:Term] =
  val conjAsms    = andIntro asms
  val conjProblem = '‹conjAsms:Term› ∧ ¬‹conjecture›'
  val conv =
    seqConv [nnf,prenex,cnf,tryConv skolemize,
             repeatConvl [binderConv,distribQuants]]
  show conjProblem
  show seqConv [nnf,prenex,cnf,repeatConvl [binderConv,distribQuants]]
         conjProblem
  val equiv = conv conjProblem
  show equiv
  theorem contr: '‹rhs (equiv: Term)› → ⊥'
    assume asm: (rhs (equiv: Term))
    show asm
    clauseThm (metis asm)
  val unmetised = unmetis (convRule (landConv (rewrConv1 (sym equiv)), contr))
  modusponens (conjAsms, unmetised)
