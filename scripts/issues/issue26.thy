theory issue26 extends \root

context
  let 'x : ℙ'
  let 'f : ℙ → ℙ'
  assume foo: '(x ↦ f = f) x'
  val bar = combine (foo, reflexive 'x')
  assert (bar : Term) == 'f x = f x'