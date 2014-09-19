theory Conversions
extends List Syntax Equal

# Identity for seqConv
val idConv   = tm => [reflexive tm]

# Zero for seqConv and identity for sumConv
val zeroConv = tm => []

# Applies one conversion to the rator and the other to the rand of a combination.
val combConv = [ratorConv,randConv] => tm =>
  show "comb"
  show tm
  match destcomb tm
    case [f,x] =>
      for fconvthm in ratorConv f do
        for xconvthm in randConv x do
          combine (fconvthm,xconvthm)
    case _         => []

# Applies a conversion to the rator of a combination    
val ratorConv = conv => combConv (conv,idConv)

# Applies a conversion to the rand of a combination
val randConv  = conv => combConv (idConv,conv)

# Applies a conversion to the body of an abstraction
val absConv = conv => tm =>
  show "abs"
  show tm
  match destabs tm
    case [ctx,x,bod] =>
      val cthms
      context <ctx>
        cthms = conv bod
      for cthm in cthms do
        abstract cthm
    case _ => []

# Converts a term appearing as the left hand side of an equation in the given list of
# theorems, to the corresponding right hand side.
val subsConv = thms => tm =>
  show "subs"
  show thms
  show tm
  for thm in thms do
    for ([l,_] if l == tm) in desteq (term thm) do
      thm

# Applies a list of conversions in sequence.      
val seqConv = convs => tm =>
  val thenConv = conv1 => conv2 => tm =>
    for '‹x› = ‹y›' as xy in conv1 tm do
      for yz in conv2 y do
        transitive (xy,yz)
  foldl (thenConv,convs,idConv) tm

# Applies a conversion as an inference rule.  
val convRule = [conv,thm] =>
  val norm = normalize (term thm)
  match term norm
    case '‹_› = ‹rhs›' =>
      for cthm in conv rhs do
        modusponens (thm, norm, cthm)

# Rewrites an instance of 'x = x' to ⊤
val reflConv = tm =>
  show "refl"
  show tm
  match tm
    case '‹x›=‹y›' if x == y => [eqTrueIntro (reflexive x)]
    case _ => []

# Attempt a conversion. If it has no results, just use idConv    
val tryConv = conv => tm =>
  match conv tm
    case []    => [reflexive tm]
    case cthms => cthms

# Applies a list of conversions non-deterministically.    
val sumConv = convs => tm =>
  for conv in convs do
    for cthm in conv tm do
      cthm

val seqWhenChangedConv = convs => tm =>
  val thenConv = conv1 => conv2 => tm =>
    for '‹x› = ‹y›' as xy if x <> y in conv1 tm do
      for yz in conv2 y do
        transitive (xy,yz)
  match convs
    case []              => idConv
    case (conv <+ convs) => foldl (thenConv,convs,conv) tm

# Applies a conversion top-down through a term, immediately retraversing a changed
# term.
def treeConv conv =
  tm =>
    tryConv (sumConv (seqWhenChangedConv (conv,tryConv (treeConv conv)),
                      combConv (treeConv conv,treeConv conv),
                      absConv (treeConv conv))) tm

