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

theorem trivImp:'∀ p. p → p'
  let 'p:ℙ'
  assume 'p:ℙ'

theorem notFalse:'¬⊥'
  modusponens [instantiate [trivImp,'⊥'],sym (apThm [notDef,'⊥'])]
