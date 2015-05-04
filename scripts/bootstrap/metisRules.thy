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

val congruence =
  theorem deleteLeft: '∀p q p2. q = ⊥ → p = p2 → (p ∨ q) = p2'
    by taut
  theorem deleteRight: '∀p. (⊥ ∨ p) = p'
    by taut
  theorem unsimp1: '∀p q. (¬q → p = ⊥) → (p ∨ q) = q'
    by taut
  theorem unsimp2: '∀p q p2. (¬q → p = p2) → (p ∨ q) = (p2 ∨ q)'
    by taut
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
    sym '¬(‹s› = ‹t›)' as thm =
      val notts = convRule (randConv symConv, thm)
      { '‹t› = ‹s›' ->
         modusponens (notts, instantiate (eqFalseIntroThm, rand (notts:Term))) }
    sym '¬(¬(‹s› = ‹t›))' as thm =
      val notts = convRule (randConv (randConv symConv), thm)
      { '¬(‹t› = ‹s›)' ->
         modusponens (notts, instantiate (eqFalseIntroThm, rand (notts:Term))) }
    sym _ = {->}
  congruence (sym,{->})

context
  let 'x'
  let 'y'
  let 'z'
  let 'P:ℙ'
  let 'Q:ℙ'
  assert ((metisRemoveSym 'x = y ∨ P ∨ x = z ∨ y = x ∨ Q'):Term) ==
            '(x = y ∨ P ∨ x = z ∨ y = x ∨ Q) = (P ∨ x = z ∨ y = x ∨ Q)'
  assert ((metisRemoveSym '¬(x = y) ∨ P ∨ x = z ∨ ¬(y = x) ∨ Q':Term)) ==
            '(¬(x = y) ∨ P ∨ x = z ∨ ¬(y = x) ∨ Q) = (P ∨ x = z ∨ ¬(y = x) ∨ Q)'

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
  by taut

def pullOut p =
  def
    conv '‹_› ∨ ‹q›' as tm if p == q = idConv tm
    conv '‹q› ∨ ‹r›' as tm if p == q = rewrConv1 orComm tm
    conv '‹q› ∨ ‹r›' as tm =
      seqConv
        [landConv conv,
         sumConv [rewrConv1 swapRight,rewrConv1 orComm]] tm
    conv '‹q›' if p == q = idConv q
    conv tm = zeroConv tm
  conv

theorem resolveLeft: '∀p q r. (p ∨ r) → (q ∨ ¬r) → (p ∨ q)'
  by taut

theorem resolveTriv1: '∀q r. r → (q ∨ ¬r) → q'
  by taut

theorem resolveTriv2: '∀p r. (p ∨ r) → ¬r → p'
  by taut

theorem finalResolve: '∀p. p → ¬p → ⊥'
  by taut
