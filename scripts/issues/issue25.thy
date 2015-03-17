theory issue25 extends \root

context
  let 'P:ℙ'
  let 'Q:ℙ'
  assert (normalize '(x ↦ y ↦ ⊤) P Q' : Term) == '(((x : ℙ ↦ y : ℙ ↦ ⊤) P) Q) = ⊤'