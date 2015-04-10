theory Conversions
extends List Syntax Equal

# Identity for seqConv
val idConv = tm => reflexive tm

# Zero for seqConv and identity for sumConv
val zeroConv = tm => nil

# Applies a list of conversions in sequence.
def seqConv convs =
  val thenConv = [conv1,conv2] => tm =>
    val xy = conv1 tm
    if xy == nil then nil
    else
      match desteq (xy: Term)
        case [_,y] =>
          match conv2 y
            case yz: Theorem => trans (xy,yz)
            case _           => nil
        case _ => nil
  foldl (thenConv,convs,idConv)

def
  sumConv [] = zeroConv
  sumConv (conv <+ convs) = tm =>
    match conv tm
      case nil  => sumConv convs tm
      case cthm => cthm

# Attempt a conversion. If it has no results, just use idConv
def tryConv conv = sumConv [conv,idConv]

def repeatConv1 c = tm => seqConv [c, tryConv (repeatConv1 c)] tm

def repeatConv c = tryConv (repeatConv1 c)

# sumConv [c, k c, k (k c), ...]
def repeatConvl [k,c] = tm => sumConv [c, repeatConvl [k,k c]] tm

# seqConv [c, k c, k (k c), ...] until failure
def seqConvl [k,c] = tm => seqConv [c, tryConv (seqConvl [k,k c])] tm

# Applies a conversion as an inference rule.
def convRule [conv,thm] =
  match conv (thm: Term)
    case nil  => nil
    case cthm => modusponens (thm,cthm)

# Applies one conversion to the rator and the other to the rand of a combination.
def combConv [ratorConv,randConv] =
  tm =>
    match destcomb tm
      case [f,x] =>
        match (ratorConv f, randConv x)
          case (fthm: Theorem, xthm: Theorem) =>
            combine (fthm, xthm)
          case _ => nil
      case _ => nil

# Applies a conversion to the rator of a combination
def ratorConv conv = combConv (conv,idConv)

# Applies a conversion to the rand of a combination
def randConv conv  = combConv (idConv,conv)

# Applies a conversion to the land of a combination
def landConv conv  = combConv (randConv conv,idConv)

# Applies a conversion to the land and rand of a binary application
def binaryConv [lconv,rconv] = combConv (randConv lconv,rconv)

# Applies a conversion to the body of an abstraction
def absConv conv =
  tm =>
    match destabs tm
      case [ctx,x,bod] =>
        val cthm
        context <ctx>
          cthm =
            match conv bod
              case nil  => nil
              case cthm => lift cthm
        match cthm
          case nil  => nil
          case cthm => assertNotNil (abstract (lift (cthm,true)))
      case _ => nil

# Converts a term appearing as the left hand side of the given equation to the
# corresponding right hand side.
def
  subsConv thm =
    tm =>
      match thm
        case '‹l› = ‹_›' if l == tm => modusponens (thm,normalize (thm: Term))
        case _                      => nil

def rewrConv1 thm =
  tm =>
    matchAntThen (thm,rhs (normalize tm),thm =>
            match thm
              case '‹_› = ‹_›' => thm
              case _           => nil)

# (Very) rudimentary rewriter.
def
  rewrConv (thms: Tuple) =
    tm =>
      repeatConv1 (sumConv (map (rewrConv1,thms))) tm
  rewrConv thm = rewrConv [thm]

# Applies a list of conversions in sequence, provided the term is changed.
val seqWhenChangedConv =
  def thenConv [conv1,conv2] =
    tm =>
      match conv1 tm
        case '‹x› = ‹y›' as xy if x <> y =>
          match conv2 y
            case '‹_› = ‹_›' as yz => trans (xy,yz)
            case _                 => nil
        case xy => xy
  convs => foldr (thenConv,convs,idConv)

# Only succeeds if the conversion changes the theorem
def changedConv conv = seqWhenChangedConv [conv]

# Applies a conversion top-down through a term, immediately retraversing a changed
# term.
def treeConv conv =
  tm =>
    tryConv (seqWhenChangedConv
               (sumConv (conv,
                         combConv (treeConv conv,treeConv conv),
                         absConv (treeConv conv)),
                treeConv conv)) tm

# Applies a conversion top-down through a term, without traversing a changed term.
def onceTreeConv conv =
  tm =>
    tryConv (sumConv (conv,
                      combConv (onceTreeConv conv,onceTreeConv conv),
                      absConv (onceTreeConv conv))) tm

# Apply a conversion bottom up
def upConv conv =
  tm =>
    seqConv [sumConv [absConv (upConv conv),
                      combConv (upConv conv, upConv conv),
                      idConv],
             tryConv conv] tm

# Rewrite x = x to ⊤
def
  reflConv '‹x› = ‹y›' if x == y = eqTrueIntro (reflexive x)
  reflConv _ = nil

# Rewrite x = y to y = x

def
  symConv '‹x› = ‹y›' =
    theorem left:
      assume asm:'‹x› = ‹y›'
      sym asm
    theorem right:
      assume asm:'‹y› = ‹x›'
      sym asm
    equivalence (left,right)
  symConv _ = nil

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
