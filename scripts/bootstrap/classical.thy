theory Classical
extends Connectives Match

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
    modusponens (conjunct1 contr,
                 matchmp (Connectives\notDef, conjunct2 contr))
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
