theory Metis
extends MetisRules

# Terms are implemented as tuples whose first element is the functor, and whose
# arguments are the (possibly 0) remaining elements. Atomic terms are variables,
# which must *not* be tuples. This is basically the s-expression encoding.

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

def comb_of_term term =
  if isVar term then term
  else mkcombs (functor term,map (comb_of_term, args term))

def map_term (f, term) =
  if isVar term then f term
  else mkTerm (functor term, for arg in args term do map_term (f, arg))

# A clause is a pair whose first element is a tuple, associating each quantifier in
# turn with a Metis free-variable [fvs,tm]
def initClause tm =
  val [_,xs,_] = stripForall tm
  [(0 to size xs - 1), tm]

# Generate n fresh variables, returning a context containing them all, and a map from
# each to the index of the implicit quantifier, outermost first. For example, given
#   freshvars 3 == [ctx, { x -> 1, y -> 2, z -> 3 }]
# lifting a theorem p out of ctx will produce ∀x y z. ‹p›
def freshvars (fvs:Tuple) =
  def
    freshs [[],freeIndex,ctx] =
      [ctx,freeIndex]
    freshs [fv <+ fvs,freeIndex,ctx] =
      ctx =
        context <ctx>
          let x:'‹fresh "x"›'
          freeIndex = freeIndex ++ { fv -> x }
      freshs (fvs,freeIndex,ctx)
  val ctx = context
  freshs (fvs,{->},ctx)

def metisInstantiate [[fvs:Tuple,cl],sub:Map] =
  val minSub = {->}
  sub =
    for [v,tm] if elem (v,fvs) in sub do
      minSub = minSub ++ {v -> tm}
    minSub
  sub =
    val subDomain = {}
    for [v,_] in sub do subDomain = subDomain ++ {v}
    for fv if not (subDomain fv) in fvs do sub = sub ++ { fv -> fv }
    sub
  val newfvs =
    val fvset = {}
    for [_,tm] in sub do
      for v in vars tm do
        fvset = fvset ++ {v}
    fvset: Tuple
  val [ctx,freeIndex] = freshvars newfvs
  context <ctx>
    for v in fvs do
      val tm = comb_of_term (map_term (freeIndex, sub v))
      cl = instantiate (cl,tm)
    cl = convRule (nubClauseConv, cl)
  [newfvs,cl]
