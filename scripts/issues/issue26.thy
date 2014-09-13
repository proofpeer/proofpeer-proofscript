theory \issue26 extends \root

context
  let 'x : ℙ'
  let 'f : ℙ → ℙ'
  assume foo: '(x ↦ f = f) x'
  show foo
  show reflexive 'x'
  # val bar = combine (foo, reflexive 'x')