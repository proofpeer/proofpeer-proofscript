theory Lift
extends Redundancies

choose isTrue: 'isTrue : 𝒰 → ℙ'
  let 'x:𝒰'
  let 'isTrue = (x = one)'

theorem unfoldLetIsTrue: '∀p c. (∀x. isTrue x = c → p (isTrue x)) = p c'
  let 'p:ℙ → ℙ'
  let 'c:ℙ'
  theorem left:
    assume asm:'∀x. isTrue x = c → p (isTrue x)'
    theorem isTrueCase:
      assume cIsTrue: 'c = ⊤'
      modusponens
        (sym cIsTrue,
          convRule (seqConv [upConv (seqConv [rewrConv isTrue, reflConv]),
                             randConv (randConv (rewrConv (sym cIsTrue)))],
                    instantiate (asm, 'one')))
    theorem isFalseCase:
      assume cIsFalse: 'c = ⊥'
      val eqFalseIntro =
        modusponens (oneNotZero, sym (instantiate (eqFalseSimp, '∅ = one')))
      convRule (seqConv [upConv (rewrConv ([isTrue, eqFalseIntro, cIsFalse]
                                           ++ tautRewrites)),
                         randConv (rewrConv (sym cIsFalse))],
                instantiate (asm, '∅'))
    matchmp (orDefEx, instantiate (boolCases, 'c'), isTrueCase, isFalseCase)
  theorem right: true
    assume pc:'p c'
    theorem imp: '∀x. isTrue x = c → p (isTrue x)'
      let 'x'
      assume asm:'isTrue x = c'
      convRule (upConv (rewrConv (sym asm)), pc)
  equivalence (left,right)

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
    val tm = termOfTree xs
    if p tm then return tm
    else
      val subterm = findSubterm (p, xs)
      if subterm <> nil then return subterm
  nil

def
  destType ':‹dom› → ‹codom›' = [dom, codom]
  destType _                  = nil

def
  mapUpTree [f,xs:Tuple] =
    f (for x in xs do mapUpTree (f,x))
  mapUpTree [f,x] = f x

def reifyBool tm =
  def reify1 tm =
    val tree = treeOfTerm tm

    def
      isProp 'isTrue ‹_›' = false
      isProp '‹_›: ℙ'     = true
      isProp _            = false

    match findSubterm (isProp, tree)
      case nil => nil
      case propTm =>
        val ('‹f›:‹ty›' <+ args) = splitLeft  (destcomb, tm)
        val argTys +> codom      = splitRight (destType, ty)

        theorem hack:
          val b = fresh "b"
          let '‹b›:ℙ'

          show propTm
          val propTree = treeOfTerm propTm
          show propTree

          def
            f tm if tm == propTree = [b]
            f tm = tm

          reflexive (termOfTree (mapUpTree (f,tree)))

        val '∀x. ‹abs› x = ‹_› x' = hack
        sym (instantiate (unfoldLetIsTrue, abs, propTm))

  show tm
  tryConv (seqConv [reify1, binderConv (binaryConv (randConv reifyBool, reifyBool))])
    tm

def litConv conv =
  def
    c ('‹_› ∨ ‹_›' as tm)     = binaryConv (c,c) tm
    c ('‹_› ∧ ‹_›' as tm)     = binaryConv (c,c) tm
    c ('‹_› = (‹_›:ℙ)' as tm) = binaryConv (c,c) tm
    c ('¬‹_›' as tm)          = randConv c tm
    c ('∀x. ‹_› x' as tm)     = binderConv c tm
    c ('∃x. ‹_› x' as tm)     = binderConv c tm
    c tm                      = conv tm
  c

def normThm thm =
  rhs (normalize (thm: Term): Term)

def metis (asms: Tuple) = metisGen (litConv reifyBool, asms)

theorem '∀a b. ∃pair. ∀x. x ∈ pair = (x = a ∨ x = b)'
  let 'a'
  let 'b'
  let 'pair = repl two (x ↦ ifThenElse (x = ∅) a b)'
  theorem '∀x. x ∈ pair = (x = a ∨ x = b)'
    by metisGen (seqConv [upConv (rewrConv existsin), litConv reifyBool],
                 [instantiate [repl, 'two', 'x ↦ ifThenElse (x = ∅) a b'],
                  ifTrue, ifFalse, two])