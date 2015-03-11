theory LogicStatements extends \root


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

context
  let 'x : 𝒰 → _ : _ → ℙ'
  assert 'x' == 'x : 𝒰 → ℙ'


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
    let '(x : 𝒰) = true'
  let '(x : ℙ) = true'


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
  assert term x_def == '∀ y. x y = y'

# the same as above, but using an intermediate theorem
context
  theorem t: '∀ y ∃ x. x = y'
    let 'y'
    let 'x = y'    
  choose x_def: 'x' t
  show x_def
  assert term x_def == '∀ y. x y = y'

# we can move the intermediate theorem into choose
context
  choose x_def: 'x : 𝒰 → _'
    theorem '∀ y ∃ x. x = y'
      let 'y'
      let 'x = y'
  show x_def
  assert term x_def == '∀ y. x y = y'

context
  failure
    choose x_def: 'x : 𝒰'
      let 'y'
      let 'x = y'

context
  val w
  theorem trivial: '∀ p. p → p' 
    w = 2
    let 'p : ℙ'
    assume 'p'
  show trivial
  assert term trivial == '∀ p. p → p'
  assert w == 2

# theorems without explicitly stating the proposition
context 
  theorem t: nil
    let 'p : ℙ'
    assume p: 'p'
    let 'a'
    p
  assert term t == '∀ p. p → p'
  theorem  
    let 'p : ℙ'
    assume p: 'p'
    let 'a'
    p
  assert term t == '∀ p. p → p'
  theorem t: true
    let 'p : ℙ'
    assume p: 'p'
    let 'a'
    p
  assert term t == '∀ p. p → (∀ a. p)'

# theorems without the theorem keyword
context 
  t: '∀ p. p → p'
    let 'p : ℙ'
    assume p: 'p'
    let 'a'
    p
  : '∀ p. p → p' 
    let 'p : ℙ'
    assume p: 'p'
    let 'a'
    p
  : '∀ p. p → (∀ a. p)'
    let 'p : ℙ'
    assume p: 'p'
    let 'a'
    p


# context
  ------------------------------------

context
  val w
  val u =
    context
      w = 2
      let 'f : 𝒰 → ℙ'
  context
    failure 'f'
  context<u>
    assert 'f' == 'f : 𝒰 → ℙ'
  assert w == 2

# context can be used as an expression, 
  but the other logic statements cannot
context
  assume 'true'
  failure (assume 'true')
  context
  failure
    failure (context)



# test *-statement behaviour 
  ------------------------------------

context
  val l =
    do*
      context
      context
      let 'x'
      let 'y = x'
      assume x: 'x = x'
      choose 'inf' infinity
      theorem 'x = x' x

  assert size l == 0
