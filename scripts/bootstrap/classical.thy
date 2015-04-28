theory Classical
extends Connectives Syntax

choose choiceDef:'epsilon:(ℙ → ℙ) → ℙ'
  let 'p:ℙ → ℙ'
  assume ex:'∃x. p x'
  choose 'chosen:ℙ' ex

theorem choice:'∀ p x. (p:ℙ → ℙ) (x:ℙ) → p (epsilon p)'
  let p:'p:ℙ → ℙ'
  let 'x:ℙ'
  assume assum:'p x'
  theorem pExists:'∃ x:ℙ. p x'
    let ydef:'(y:ℙ) = x'
    modusponens (assum,combine (reflexive p,sym ydef))
  modusponens (pExists,instantiate (choiceDef,'p:ℙ → ℙ'))

theorem excludedMiddle: '∀p. p ∨ ¬p'
  let 'p:ℙ'
  val u = '(x ↦ x ∨ p)'
  val v = '(x ↦ ¬x ∨ p)'
  theorem lemma:'(epsilon ‹u› ∧ ¬(epsilon ‹v›)) → p → ⊥'
    assume asm:'epsilon ‹u› ∧ ¬(epsilon ‹v›)'
    assume p:'p:ℙ'
    val eq =
      trans
        (treeConv (rewrConv [eqTrueIntro p,orRightZero]) 'epsilon ‹u›',
           sym (treeConv (rewrConv [eqTrueIntro p,orRightZero]) 'epsilon ‹v›'))
    val contr = convRule (treeConv (rewrConv [eq]),asm)
    modusponens (conjuncts contr 0,
                 matchmp (notDefEx, conjuncts contr 1))
  theorem lemma2: '(epsilon ‹u› ∧ ¬(epsilon ‹v›)) → p ∨ ¬p'
    assume asm:'epsilon ‹u› ∧ ¬(epsilon ‹v›)'
    orIntroR ('p:ℙ',convRule (treeConv (rewrConv [impliesNot]),
                              modusponens (asm,lemma)))
  theorem lemma3: 'p → p ∨ ¬p'
    assume p:'p:ℙ'
    orIntroL (p,'¬p')
  val factored = matchmp
        (sym (instantiate (orAndDistrib2,
              'epsilon ‹u›',
              '¬(epsilon ‹v›)',
              'p:ℙ')),
         andIntro (matchmp (instantiate (choice,u), orIntroL (truth,'p:ℙ')),
                   matchmp (instantiate (choice,v), orIntroL (notFalse,'p:ℙ'))))
  matchmp (orDefEx, factored, lemma2, lemma3)

theorem boolCases: '∀p. p = ⊤ ∨ p = ⊥'
  convRule (randConv (absConv (binaryConv (rewrConv1 (gsym eqTrueSimp),
                                           rewrConv1 (gsym eqFalseSimp)))),
            excludedMiddle)

# Remove all outer universal quantifiers, returning the variables and a context in
# which those variables have been defined.
def
  stripForall '∀x. ‹p› x' =
    val [ctx,x,body] = destabs p
    context <ctx>
      match stripForall body
        case [nil,[],body] => return [ctx,[x],body]
        case [ctx,xs,body] =>
          context <ctx>
            return [ctx,x <+ xs,body]
  stripForall '‹x›' = [nil,[],x]

theorem reflPropTrue: '∀p:ℙ. (p = p) = ⊤'
  let 'p:ℙ'
  eqTrueIntro (reflexive 'p:ℙ')

theorem reflImpTrue: '∀p:ℙ. (p → p) = ⊤'
  let p:'p:ℙ'
  theorem imp:
    assume p
  eqTrueIntro imp

val tautRewrites =
  [notFalseTrue,notTrueFalse,
   orRightZero,orRightId,
   convRule (onceTreeConv (rewrConv1 orComm), orRightZero),
   convRule (onceTreeConv (rewrConv1 orComm), orRightId),
   andRightZero,andRightId,
   convRule (onceTreeConv (rewrConv1 andComm), andRightZero),
   convRule (onceTreeConv (rewrConv1 andComm), andRightId),
   reflPropTrue,
   instantiate (eqTrueSimp, '⊥'),
   convRule (randConv (absConv (landConv symConv)), eqTrueSimp),
   convRule (randConv (rewrConv1 notTrueFalse),instantiate (eqFalseSimp,'⊤')),
   convRule (randConv (rewrConv1 notTrueFalse),
     instantiate
       (convRule (randConv (absConv (landConv symConv)), eqFalseSimp),'⊤')),
   topDefEq,point,botDefEq,
   convRule (treeConv (rewrConv1 notTrueFalse), instantiate (gsym notDefEx,'⊤'))
   ]

val truthTables =
  def
    ground '∀p. ‹_› p' as thm =
      [instantiate (thm, '⊤'), instantiate (thm, '⊥')]
    ground thm = [thm]
  for thm in tautRewrites do
    for gthm in ground thm do
      gthm

# Tautology verifier.
def taut tm =
  def
    atoms '⊤'            = {}
    atoms '⊥'            = {}
    atoms '‹p› ∧ ‹q›'     = atoms p ++ atoms q
    atoms '‹p› ∨ ‹q›'     = atoms p ++ atoms q
    atoms '‹p› → ‹q›'     = atoms p ++ atoms q
    atoms '(‹p›:ℙ) = ‹q›' = atoms p ++ atoms q
    atoms '¬‹p›'          = atoms p
    atoms '‹p›:ℙ'         = {p}
    atoms _               = {}
  def
    tautAux [tm,(x <+ xs),rewrsAcc] =
      val '‹p› ∨ ‹notp›' as caseSplit = instantiate (boolCases,x)
      theorem tautology:
        theorem pCase:
          assume p:p
          tautAux (tm, xs, (p <+ rewrsAcc))
        theorem notpCase:
          assume notp:notp
          tautAux (tm, xs, (notp <+ rewrsAcc))
        matchmp (orDefEx,caseSplit,pCase,notpCase)
    tautAux ['‹p›:ℙ',[],rewrsAcc] =
      eqTrueElim (upConv (sumConv (map (subsConv,rewrsAcc))) p)
  val [ctx,xs,body] = stripForall tm
  context <ctx>
      return tautAux (body, atoms body:Tuple, truthTables)

choose hilbertChoiceDef: 'epsilonU:(𝒰 → ℙ) → 𝒰'
  let 'p:𝒰 → ℙ'
  assume ex:'∃x. p x'
  choose 'chosen' ex

theorem hilbertChoice:'∀ p x. p x → p (epsilonU p)'
  let p:'p:𝒰 → ℙ'
  let 'x'
  assume assum:'p x'
  theorem pExists:'∃ x. p x'
    let ydef:'y = x'
    modusponens (assum,combine (reflexive p,sym ydef))
  modusponens (pExists,instantiate (hilbertChoiceDef,'p'))

# Should write a function for a more general definition scheme which returns the
# theorem eta-expanded.
let ifThenElse:'ifThenElse = (p x y ↦ epsilonU (z ↦ (p → z = x) ∧ (¬p → z = y)))'
theorem ifThenElseEx:
          '∀p x y. ifThenElse p x y = epsilonU (z ↦ (p → z = x) ∧ (¬p → z = y))'
  let p:'p:ℙ'
  let x:'x'
  let y:'y'
  combine [ifThenElse, reflexive p, reflexive x, reflexive y]

theorem ifTrue: '∀x y. ifThenElse ⊤ x y = x'
  let 'x'
  let 'y'
  val 'ifThenElse ⊤ x y = epsilonU ‹description›' as thm =
    convRule (upConv (rewrConv tautRewrites), instantiate (ifThenElseEx,'⊤','x','y'))
  transitive
    (thm, modusponens (reflexive 'x',instantiate [hilbertChoice, description, 'x']))

theorem ifFalse: '∀x y. ifThenElse ⊥ x y = y'
  let 'x'
  let 'y'
  val 'ifThenElse ⊥ x y = epsilonU ‹description›' as thm =
    convRule (upConv (rewrConv tautRewrites), instantiate (ifThenElseEx,'⊥','x','y'))
  transitive
    (thm, modusponens (reflexive 'y',instantiate [hilbertChoice, description, 'y']))
