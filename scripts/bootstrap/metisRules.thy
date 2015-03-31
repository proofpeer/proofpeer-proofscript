theory MetisRules
extends CNFConv

def
  noArgs tm =
    match destcomb tm
      case [f,x] => noArgs f + 1
      case _     => 0

def tryConvL [k,c] = sumConv [k c, c]

def tryRand tm =
  match rand tm
    case r => r
    case _ => tm

val followPath =
  def
    follow [[],tm,acc]      = [acc,tm]
    follow [i <+ is,tm,acc] =
      val ri = noArgs tm - i - 1
      follow [is,tryRand (iterate [ri,rator,tm]),acc +> ri]
  [is,tm] => follow [is,tm,[]]

def metisxiom thm = thm
def metisAssume p = instantiate (excludedMiddle,p)
def metisRefl x = reflexive x
def metisEquality [is,lit,rhs] =
  val flipImpliesCNF =
    convRule (binderConv (binderConv (randConv (rewrConv1 orComm))), impliesCNF)
  val [ris,lhs] = followPath [is,lit]
  theorem imp:
    assume lit
    assume eq:'‹lhs› = ‹rhs›'
    def
      equality []          = subsConv eq
      equality (ri <+ ris) =
        iterate
          [ri,
           ratorConv,
           tryConvL [randConv,equality ris]]
    equality ris lit
  convRule (seqConv [rewrConv impliesCNF, randConv (rewrConv impliesCNF)], imp)

val congruence =
  theorem deleteLeft: '∀p q p2. q = ⊥ → p = p2 → (p ∨ q) = p2'
    taut '∀p q p2. q = ⊥ → p = p2 → (p ∨ q) = p2'
  theorem deleteRight: '∀p. (⊥ ∨ p) = p'
    taut '∀p. (⊥ ∨ p) = p'
  theorem unsimp1: '∀p q. (¬q → p = ⊥) → (p ∨ q) = q'
    taut '∀p q. (¬q → p = ⊥) → (p ∨ q) = q'
  theorem unsimp2: '∀p q p2. (¬q → p = p2) → (p ∨ q) = (p2 ∨ q)'
    taut '∀p q p2. (¬q → p = p2) → (p ∨ q) = (p2 ∨ q)'
  def
    congruence [mkRefutes,refute] = tm =>
      match tm
        case '‹p› ∨ ‹q›' =>
          val notQ = refute q
          if notQ == nil then
            theorem qConv:
              assume notqAsm: '¬‹q›'
              congruence (mkRefutes, refute ++ mkRefutes notqAsm) p
            val unsimped = matchmp (instantiate (unsimp1, p, q), qConv)
            if unsimped == nil then
              unsimped = matchmp (instantiate (unsimp2, p, q), qConv)
            unsimped
          else
            matchmp (instantiate (deleteLeft, p),
                     notQ,
                     congruence (mkRefutes,refute) p)
        case '‹p›' =>
          val notP = refute p
          if notP == nil then reflexive p else notP
  congruence

val eqFalseIntroThm = gsym eqFalseSimp

val metisRemoveSym =
  def
    notSym '¬(‹s› = ‹t›)' as thm =
      val notts = convRule (randConv symConv, thm)
      { '‹t› = ‹s›' ->
         modusponens (notts, instantiate (eqFalseIntroThm, rand (notts:Term))) }
    notSym _ = {->}
  congruence (notSym,{->})

val metisRemoveIrrefl =
  theorem notIrreflThm: '∀x. (¬x = x) = ⊥'
    let 'x'
    modusponens (reflexive 'x', instantiate [taut '∀p. p → (¬p) = ⊥','x = x'])
  def
    notIrreflConv '¬(‹x› = ‹y›)' if x == y as tm =
      instantiate (notIrreflThm, x)
    notIrreflConv _ = nil
  thm =>
    val conv =
      upConv (sumConv [notIrreflConv,rewrConv1 orLeftId, rewrConv1 orRightId])
    convRule (conv, thm)

val nubClauseConv =
  def eqFalseIntro '¬‹p›' as thm =
    { p -> modusponens (thm, instantiate (eqFalseIntroThm,p)) }
  congruence (eqFalseIntro,{->})

theorem swapRight: '∀p q r. ((p ∨ q) ∨ r) = ((p ∨ r) ∨ q)'
  taut '∀p q r. ((p ∨ q) ∨ r) = ((p ∨ r) ∨ q)'

def pullOut p =
  def
    conv '‹_› ∨ ‹q›' as tm if p == q = idConv tm
    conv '‹q› ∨ ‹r›' as tm =
      seqConv
        [landConv conv,
         sumConv [rewrConv1 swapRight,rewrConv1 orComm]] tm
    conv '‹q›' if p == q = idConv q
    conv tm = zeroConv tm
  conv

theorem resolveLeft: '∀p q r. (p ∨ r) → (q ∨ ¬r) → (p ∨ q)'
  taut '∀p q r. (p ∨ r) → (q ∨ ¬r) → (p ∨ q)'

theorem resolveTriv1: '∀q r. r → (q ∨ ¬r) → q'
  taut '∀q r. r → (q ∨ ¬r) → q'

theorem resolveTriv2: '∀p r. (p ∨ r) → ¬r → p'
  taut '∀p r. (p ∨ r) → ¬r → p'

def
  negate '¬‹p›' = p
  negate p      = '¬‹p›'

def metisResolution [lit,pos,neg] =
  val pos1 = convRule (pullOut lit, pos)
  val neg1 = convRule (pullOut (negate lit), neg)
  val res  = matchmp (resolveLeft, pos1, neg1)
  if res == nil then
    res = matchmp (resolveTriv1, pos1, neg1)
  if res == nil then
    res = matchmp (resolveTriv2, pos1, neg1)
  convRule (nubClauseConv, res)

context
  let 'p:ℙ'
  let 'q:ℙ'
  let 'r:ℙ'
  let 's:ℙ'
  let 't:ℙ'
  show nubClauseConv 'p ∨ p ∨ p ∨ p ∨ p'
  def eqFalseIntro '¬‹p›' as thm =
    modusponens (thm, instantiate (gsym eqFalseSimp,p))
  show rhs (normalize (pullOut 'q' 'p ∨ q ∨ r ∨ s ∨ t': Term): Term)
  assume asm1: 'q ∨ p ∨ t'
  assume asm2: '¬q ∨ s ∨ ¬p'
  show metisResolution ['p:ℙ',asm1,asm2]

context
  let 'f: 𝒰 → 𝒰 → 𝒰 → 𝒰 → ℙ'
  let 'g: 𝒰 → 𝒰 → 𝒰'
  let 'h: 𝒰 → 𝒰 → 𝒰'
  let 'x: 𝒰'
  let 'y: 𝒰'
  let 'z: 𝒰'
  let 'w: 𝒰'
  let 'u: 𝒰'
  let 'v: 𝒰'
  let 'a: 𝒰'
  let 'p:ℙ'
  let 'q:ℙ'
  let 'r:ℙ'
  assume asm1: '(u = v) ∨ (x = y) ∨ r ∨ (x = y) ∨ (y = x) ∨ p ∨ (v = u) ∨ q'
  assume asm2: '¬x = x ∨ p ∨ ¬y = z ∨ ¬y = y'
  show followPath [[1,0],'f x (g u v) z w']
  show metisEquality [[1,0],'f x (g u v) z w','h a z']
  show metisRemoveSym asm1
  show rhs (normalize (metisRemoveIrrefl asm2: Term))
