theory Classical
extends Connectives Match

theorem impliesNot: '∀p. (p → ⊥) = (p = ⊥)'
  let 'p:ℙ'
  theorem left: '(p → ⊥) → (p = ⊥)'
    assume asm:'p → ⊥'
    equivalence (asm, instantiate (botDef,'p:ℙ'))
  theorem right: '(p = ⊥) → (p → ⊥)'
    assume asm:'p = ⊥'
    convRule (randConv (rewrConv [asm]),instantiate (trivImp,'p:ℙ')) 0
  equivalence (left,right)

def
  eqFalseIntro '¬‹p›' as thm = modusponens (thm,instantiate (simpNP,p))
  eqFalseIntro thm           = assertThm thm

theorem eqFalseEq: '∀p. (p = ⊥) = (¬p)'
  let 'p:ℙ'
  theorem left: '(p = ⊥) → ¬p'
    assume asm:'p = ⊥'
    convRule (randConv (rewrConv [sym asm]), notFalse) 0
  equivalence (left,instantiate (simpNP,'p:ℙ'))

choose choiceDef:'epsilon:(ℙ → ℙ) → ℙ'
  let 'p:ℙ → ℙ'
  assume ex:'∃x. p x'
  choose 'chosen:ℙ' ex

theorem choice:'∀ p x. (p:ℙ → ℙ) (x:ℙ) → p (epsilon p)'
  let p:'p:ℙ → ℙ'
  let 'x:ℙ'
  assume assum:'p x'
  theorem pExists:'∃ x:ℙ. p x'
    let ydef:'y:ℙ = x'
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
      trans (treeConv (rewrConv [eqTrueIntro p,orRightZero]) 'epsilon ‹u›' 0,
             sym (treeConv (rewrConv [eqTrueIntro p,orRightZero]) 'epsilon ‹v›' 0))
    val [contr] = convRule (treeConv (rewrConv [eq]),asm)
    modusponens (conjuncts contr 0,
                 matchmp (notDefEx, conjuncts contr 1))
  theorem lemma2: '(epsilon ‹u› ∧ ¬(epsilon ‹v›)) → p ∨ ¬p'
    assume asm:'epsilon ‹u› ∧ ¬(epsilon ‹v›)'
    orIntroR ('p:ℙ',convRule (treeConv (rewrConv [impliesNot,eqFalseEq]),
                              modusponens (asm,lemma)) 0)
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
  matchmp (Connectives\orDef, factored, lemma2, lemma3)

theorem orComplement: '∀p. (p ∨ ¬p) = ⊤'
  let p:'p:ℙ'
  eqTrueIntro (instantiate (excludedMiddle,p))

def
  transImp ['‹p› → ‹q›' as thm] =
    val _ = assertThm thm
    thm
  transImp (('‹p› → ‹q›' as imp) <+ imps) =
    theorem thm:
      assume p:'‹p›'
      modusponens (modusponens (p,imp),transImp imps)
    thm

theorem negInvolve: '∀p. (¬(¬p)) = p'
  let 'p:ℙ'
  theorem left:
    assume nnp:'¬(¬p)'
    theorem npp:
      assume np:'¬p'
      matchmp (andComplement, andIntro (np,nnp))
    matchmp (\bootstrap\Connectives\orDef,
             instantiate (excludedMiddle, 'p:ℙ'),
             instantiate (trivImp, 'p:ℙ'),
             transImp (npp, instantiate (botDef, 'p:ℙ')))
  theorem right:
    assume asm:'p:ℙ'
    theorem npp:
      assume np:'¬p'
      matchmp (andComplement, andIntro (asm,np))
    matchmp (gsym notDefEx, npp)
  equivalence (left,right)

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
