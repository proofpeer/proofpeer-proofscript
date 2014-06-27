theory \examples\LogicStatements extends \root

# let introduction

context
  failure 'x'
  let 'x'
  assert 'x' == 'x : 𝒰'
  failure 'x : ℙ'
  failure
    let 'x'

context
  failure 'x'
  let x: 'x : ℙ'
  assert x == 'x' == 'x : ℙ'
  failure 'x : 𝒰'

context
  failure 'x'
  val x = "x"
  let x
  assert 'x' == 'x : 𝒰'


# let definition

context
  failure 'x'
  let x_def: 'x = ∅ ∪ {∅}'
  show x_def
  assert 'x' == 'x : 𝒰'
  assert term x_def == 'x = ∅ ∪ {∅}'

context
  failure 'x'
  val x_def = 
    let 'x = ∅ ∪ {∅}'
  show x_def
  assert 'x' == 'x : 𝒰'
  assert term x_def == 'x = ∅ ∪ {∅}'

context
  failure 'x'
  let x_def: 'x = true'
  assert 'x' == 'x : ℙ'
  assert term x_def == 'x = true'

context
  failure 'x'
  failure
    let 'x : 𝒰 = true'
  let 'x : ℙ = true'

