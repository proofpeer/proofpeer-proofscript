theory Conversions
extends List Syntax Equal Match

# Identity for seqConv
val idConv   = tm => [reflexive tm]

# Zero for seqConv and identity for sumConv
val zeroConv = tm => []

# Applies one conversion to the rator and the other to the rand of a combination.
def combConv [ratorConv,randConv] =
  tm =>
    match destcomb tm
      case [f,x] =>
        for fconvthm in ratorConv f do
          for xconvthm in randConv x do
            combine (fconvthm,xconvthm)
      case _         => []

# Applies a conversion to the rator of a combination
def ratorConv conv = combConv (conv,idConv)

# Applies a conversion to the rand of a combination
def randConv conv  = combConv (idConv,conv)

# Applies a conversion to the lhand and rand of a binary application
def binaryConv [lconv,rconv] =
  combConv (randConv lconv,rconv)

# Applies a conversion to the body of an abstraction
def absConv conv =
  tm =>
    match destabs tm
      case [ctx,x,bod] =>
        val cthms
        context <ctx>
          cthms = (for cthm in conv bod do
                     lift cthm)
        for cthm in cthms do
          abstract (lift (cthm,true))
      case _ => []

# Converts a term appearing as the left hand side of an equation in the given list of
# theorems, to the corresponding right hand side.
def subsConv thms =
  tm =>
    for thm in thms do
      for ([l,_] if l == tm) in [desteq thm] do
        thm

def rewrConv thms =
  tm =>
    concat (for thm in thms do
              val matchedEqs =
                matchAntThen (thm,tm,
                  thm =>
                    match thm
                      case '‹_› = ‹_›' => [thm]
                      case _           => [])
              if matchedEqs == nil then
                []
              else
                matchedEqs)

# Applies a list of conversions in sequence.
def seqConv convs =
  tm =>
    val thenConv = conv1 => conv2 => tm =>
      for '‹x› = ‹y›' as xy in conv1 tm do
        for yz in conv2 y do
          trans (xy,yz)
    foldl (thenConv,convs,idConv) tm

# Applies a conversion as an inference rule.
def convRule [conv,thm] =
  val norm = normalize (term thm)
  match norm
    case '‹_› = ‹rhs›' =>
      for cthm in conv rhs do
        modusponens (thm, norm, cthm)

# Rewrites an instance of 'x = x' to ⊤
val reflConv = tm =>
  match tm
    case '‹x›=‹y›' if x == y => [eqTrueIntro (reflexive x)]
    case _ => []

# Attempt a conversion. If it has no results, just use idConv
def tryConv conv =
  tm =>
    match conv tm
      case []    => [reflexive tm]
      case cthms => cthms

# Applies a list of conversions non-deterministically.
def sumConv convs =
  tm =>
    for conv in convs do
      for cthm in conv tm do
        cthm

def seqWhenChangedConv convs =
  tm =>
    val thenConv = conv1 => conv2 => tm =>
      for '‹x› = ‹y›' as xy if x <> y in conv1 tm do
        for yz in conv2 y do
          trans (xy,yz)
    match convs
      case []              => idConv
      case (conv <+ convs) => foldl (thenConv,convs,conv) tm

# Applies a conversion top-down through a term, immediately retraversing a changed
# term.
def treeConv conv =
  tm =>
    tryConv (seqWhenChangedConv
               (sumConv (conv,
                         combConv (treeConv conv,treeConv conv),
                         absConv (treeConv conv)),
                treeConv conv)) tm
