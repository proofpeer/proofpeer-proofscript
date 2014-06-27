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

context
  let 'x'
  theorem 'x = x'
    reflexive 'x'


# combine
  ------------------------------------

context
  let 't1'
  let eq1: 's1 = t1'
  let 't2 : _ → _'
  let eq2: 's2 = t2' 
  let 't3 : (_ → _) → (_ → _)'
  let eq3: 's3 = t3'
  
  theorem 's1 = t1'
    combine [eq1]
  theorem 's2 s1 = t2 t1'
    combine (eq2, eq1)
  theorem 's2 (s2 s1) = t2 (t2 t1)'
    combine (eq2, combine (eq2, eq1))
  theorem 's3 s2 s1 = t3 t2 t1'
    combine (eq3, eq2, eq1)
  failure combine (eq1)
  failure combine []




