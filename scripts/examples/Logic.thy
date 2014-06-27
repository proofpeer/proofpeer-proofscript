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
