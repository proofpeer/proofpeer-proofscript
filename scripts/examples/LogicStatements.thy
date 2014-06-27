theory \examples\LogicStatements extends \root


# let introduction
  ------------------------------------

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
  ------------------------------------

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


# assume
  ------------------------------------

context
  assume f: 'false'
  show f
  assert term f == 'false'

context
  val f = assume "false"
  show f
  assert term f == 'false'


# choose and theorem
  ------------------------------------

context
  choose x_def: 'x' 
    let 'y'
    let 'x = y'
  show x_def
  assert term x_def == 'y ↦ (x y) = y'

# the same as above, but using an intermediate theorem
context
  theorem t: '∀ y ∃ x. x = y'
    let 'y'
    let 'x = y'    
  choose x_def: 'x' t
  show x_def
  assert term x_def == 'y ↦ (x y) = y'

# we can move the intermediate theorem into choose
context
  choose x_def: 'x'
    theorem '∀ y ∃ x. x = y'
      let 'y'
      let 'x = y'
  show x_def
  assert term x_def == 'y ↦ (x y) = y'



