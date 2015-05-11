theory Lift
extends Redundancies

def normThm thm =
  modusponens [thm, normalize (thm: Term)]

table<context> unfoldLetThm a =
  theorem '∀p c. (∀x:‹a›. x = c → p x) = p c'
    val p = fresh "p"
    val c = fresh "c"
    let '‹p›:‹a› → ℙ'
    let '‹c›:‹a›'
    theorem left: '(∀x. x = ‹c› → ‹p› x) → ‹p› ‹c›'
      assume asm:'∀x. x = ‹c› → ‹p› x'
      modusponens (reflexive '‹c›', instantiate (asm, '‹c›'))
    theorem right: '‹p› ‹c› → (∀x. x = ‹c› → ‹p› x)'
      assume pc:'‹p› ‹c›'
      val x = fresh "x"
      let '‹x›:‹a›'
      assume xy:'‹x› = ‹c›'
      convRule (randConv (subsConv (sym xy)), pc)
    equivalence (left,right)

# TODO: This obviously needs a more general mechanism.
theorem inductBool: '∀p. (p ⊤ ∧ p ⊥) = (∀b. p b)'
  let 'p:ℙ → ℙ'
  theorem left: true
    assume asm:'p ⊤ ∧ p ⊥'
    let 'b:ℙ'
    theorem bIsTrue:
      assume b:'b = ⊤'
      rewriteRule (sym b, conjuncts asm 0)
    theorem bIsFalse:
      assume b:'b = ⊥'
      rewriteRule (sym b, conjuncts asm 1)
    matchmp (orDefEx, instantiate (boolCases, 'b'), bIsTrue, bIsFalse)
  theorem right:
    assume asm:'∀b. p b'
    andIntro (instantiate (asm,'⊤'), instantiate (asm,'⊥'))
  equivalence (left,right)

def
  mapUpTree [f,xs:Tuple] =
    f (for x in xs do mapUpTree (f,x))
  mapUpTree [f,x] = f x

def
  termOfTree [f] = f
  termOfTree (splits:Tuple) =
    mkcombs (for split in splits do termOfTree split)

def treeOfTerm tm =
  if destcomb tm == nil then [tm] else
    for arg in splitLeft (destcomb,tm) do
      treeOfTerm arg

def findSubterm (p, (f <+ xss:Tuple)) =
  for xs:Tuple in xss do
    val subterm = findSubterm (p, xs)
    if subterm == nil then
      val tm = termOfTree xs
      if p tm then return tm
    else
      return subterm
  nil

def mapTreeGen [f,xs:Tuple,init] =
  val next = init
  f (for x in xs do
       val [y,next2] = mapUpTree (f,x,next)
       next = next2
       if y == nil then return nil else y)

def litConv conv =
  def
    c ('‹_› ∨ ‹_›' as tm)     = binaryConv (c,c) tm
    c ('‹_› ∧ ‹_›' as tm)     = binaryConv (c,c) tm
    c ('‹_› = (‹_›:ℙ)' as tm) = binaryConv (c,c) tm
    c ('‹_› → (‹_›)'   as tm) = binaryConv (c,c) tm
    c ('¬‹_›' as tm)          = randConv c tm
    c ('∀x. ‹_› x' as tm)     = binderConv c tm
    c ('∃x. ‹_› x' as tm)     = binderConv c tm
    c tm                      = conv tm
  c

def reifyBool tm =
  def reify1 tm =
    val tree = treeOfTerm tm

    def
      isProp '⊤'          = false
      isProp '⊥'          = false
      isProp '‹_›: ℙ'     = true
      isProp _            = false

    match findSubterm (isProp, tree)
      case nil => idConv tm
      case propTm if propTm == tm => idConv tm
      case propTm =>
        theorem hack1:
          val b = fresh "b"
          let '‹b›:ℙ'

          val propTree = treeOfTerm propTm

          def
            f tm if tm == propTree = [b]
            f tm = tm

          reflexive (termOfTree (mapUpTree (f,tree)))

        theorem hack2:
          val b = fresh "b"
          let '‹b›:ℙ'

          val propTree = treeOfTerm propTm

          def
            f tm if tm == propTree = [b]
            f tm = tm

          reflexive '‹b› = ‹propTm› → ‹termOfTree (mapUpTree (f,tree))›'

        val '∀x. ‹abs1› x = ‹_› x' = hack1
        val '∀x. ‹abs2› x = ‹_› x' = hack2

        # TODO: Use new lifting of terms rather than hacks
        val simps =
          val c = binderConv (landConv symConv)
          [convRule (c, eqTrueSimp), convRule (c, eqFalseSimp)]
        val c = landConv (rewrConv simps)
        convRule
          (randConv (seqConv [rewrConv (gsym (instantiate (inductBool, abs2))),
                              binaryConv [c,c],
                              reifyBool]),
           normThm (sym (instantiate (unfoldLetThm ':ℙ', abs1, propTm))))
  litConv reify1 tm

val metisPreConv =
  seqConv [upConv (sumConv [expandForallIn, expandExistsIn]),reifyBool]
