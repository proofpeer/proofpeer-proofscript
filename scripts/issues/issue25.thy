theory \issue25 extends \root

context
  let 'P:ℙ'
  let 'Q:ℙ'
  assert term (normalize '(x ↦ y ↦ ⊤) P Q') == '(((x : ℙ ↦ y : ℙ ↦ ⊤) P) Q) = ⊤'