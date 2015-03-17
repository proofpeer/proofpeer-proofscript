theory Conversions
extends List Syntax Equal Match

# Identity for seqConv
val idConv = tm => [reflexive tm]

# Zero for seqConv and identity for sumConv
val zeroConv = tm => []

# Applies one conversion to the rator and the other to the rand of a combination.
def combConv [ratorConv,randConv] =
  tm =>
    match destcomb tm
      case [f,x] =>
        for fconvthm in ratorConv f do
          for xconvthm in randConv x do
            assertNotNil (combine (fconvthm,xconvthm))
      case _         => []

# Applies a conversion to the rator of a combination
def ratorConv conv = combConv (conv,idConv)

# Applies a conversion to the rand of a combination
def randConv conv  = combConv (idConv,conv)

# Applies a conversion to the land of a combination
def landConv conv  = combConv (randConv conv,idConv)

# Applies a conversion to the land and rand of a binary application
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
          assertNotNil (abstract (lift (cthm,true)))
      case _ => []

# Converts a term appearing as the left hand side of an equation in the given list of
# theorems, to the corresponding right hand side.
def subsConv thms =
  tm =>
    for thm in thms do
      for ([l,_] if l == tm) in [desteq thm] do
        thm

# Non-deterministic rewriter.
def rewrConvND thms =
  tm =>
    concat
      (for thm in thms do
         val matchedEqs =
           matchAntThen (thm,tm,thm =>
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
      for '‹_› = ‹y›' as xy in conv1 tm do
        for '‹_› = ‹_›' as yz in conv2 y do
          assertNotNil (trans (xy,yz))
    foldl (thenConv,convs,idConv) tm

# Applies a conversion as an inference rule.
def convRule [conv,thm] =
  for '‹_› = ‹_›' as cthm in conv (thm : Term) do
    modusponens (thm, cthm)

# Attempt a conversion. If it has no results, just use idConv
def tryConv conv =
  tm =>
    match conv tm
      case []    => idConv tm
      case cthms => cthms

# Applies a list of conversions non-deterministically.
def sumConvND convs =
  tm =>
    for conv in convs do
      for '‹_› = ‹_›' as cthm in conv tm do
        cthm

def
  sumConv [] = zeroConv
  sumConv (conv <+ convs) = tm =>
    match conv tm
      case []    => sumConv convs tm
      case cthms => cthms

# Applies a list of conversions in sequence, requiring each to succed.
def seqWhenChangedConv convs =
  tm =>
    val thenConv = conv1 => conv2 => tm =>
      for '‹x› = ‹y›' as xy if x <> y in conv1 tm do
        for '‹_› = ‹_›' as yz in conv2 y do
          assertNotNil (trans (xy,yz))
    match convs
      case []              => idConv
      case (conv <+ convs) => foldl (thenConv,convs,conv) tm

# Only succeeds if the conversion changes the theorem
def changedConv conv = seqWhenChangedConv [conv, idConv]

# Deterministic rewriter.
def
  rewrConv []                 = zeroConv
  rewrConv (thm <+ _) as thms =
    val rewrs =
      for thm in thms do
        tryConv (rewrConvND [thm])
    changedConv (seqConv rewrs)
  rewrConv thm = rewrConv [thm]

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
  reflConv '‹x› = ‹y›' if x == y = [eqTrueIntro (reflexive x)]
  reflConv _ = []

# Rewrite x = y to y = x
def symConv '‹x› = ‹y›' =
  theorem left:
    assume asm:'‹x› = ‹y›'
    sym asm
  theorem right:
    assume asm:'‹y› = ‹x›'
    sym asm
  [equivalence (left,right)]

def repeatConv1 c = tm => seqConv [c, tryConv (repeatConv1 c)] tm

def repeatConv c = tryConv (repeatConv1 c)

# Repeat a conversional.
def repeatConvl [k,c] = tm => sumConv [seqConv [c, repeatConvl [k,k c]], c] tm

assert map (t => t : Term, absConv (tm => [reflexive tm]) 'x ↦ ⊤') == ['(x ↦ ⊤) = (x ↦ ⊤)']

assert map (t => t : Term, absConv idConv 'x ↦ ⊤') == ['(x ↦ ⊤) = (x ↦ ⊤)']

assert map (t => t : Term, absConv (subsConv [reflexive '⊤']) 'x ↦ ⊤') == ['(x ↦ ⊤) = (x ↦ ⊤)']
