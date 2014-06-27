theory \examples\Logic extends \root


# term
  ------------------------------------

context
  let 'x'
  assert term 'x' == 'x'
  assert term "x" == 'x'
  assume x: 'x = x'
  assert term x == 'x = x'
  
context
  let 'x'
  val t
  context
    let 'y' 
    t = assume 'x = y'
    assert term t == 'x = y'
  assert term t == '∀ y. x = y → x = y'


# transitive
  ------------------------------------

context
  let 'x1'
  let 'x2'
  let 'x3'
  let 'x4'
  assume t12: 'x1 = x2'
  assume t23: 'x2 = x3'
  assume t34: 'x3 = x4'
  theorem t14: 'x1 = x4'
    transitive (t12, t23, t34)
  theorem 'x1 = x2'
    transitive [t12]
  failure transitive []
  failure transitive t12

# reflexive
  ------------------------------------

