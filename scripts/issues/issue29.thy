theory \issue29 extends \root

theorem '∀ p. p → (true = ((p : ℙ ↦ p) = (p ↦ p)))'
  let 'p:ℙ'
  assume 'p'
  trueDef
