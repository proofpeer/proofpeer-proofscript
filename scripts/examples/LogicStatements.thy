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
  let '‹x›'
  assert 'x' == 'x : 𝒰'

context
  let 'x : 𝒰 → _ : _ → ℙ'
  assert 'x' == 'x : 𝒰 → ℙ'

context 
  let '‹val x› : ℙ'
  val y = 2
  let '‹= y›'
  failure let '‹val z› = ‹val x›'
  let '‹val z› = ‹x›'  
  let w: '‹val w› = x' 
  def isTerm(t : Term) = true
  def isTheorem(th : Theorem) = true
  show x
  show y
  show z
  assert isTerm x
  assert isTerm y
  assert isTerm z
  failure (isTerm w) 
  assert isTheorem w

# let definition
  ------------------------------------

context
  failure 'x'
  let x_def: 'x = ∅ ∪ {∅}'
  show x_def
  assert 'x' == 'x : 𝒰'
  assert (x_def : Term) == 'x = ∅ ∪ {∅}'

context
  failure 'x'
  val x_def = 
    let 'x = ∅ ∪ {∅}'
  show x_def
  assert 'x' == 'x : 𝒰'
  assert (x_def : Term) == 'x = ∅ ∪ {∅}'

context
  failure 'x'
  let x_def: 'x = true'
  assert 'x' == 'x : ℙ'
  assert (x_def : Term) == 'x = true'

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
  assert (f : Term) == 'false'

context
  val f = assume "false"
  show f
  assert (f : Term) == 'false'


# choose and theorem
  ------------------------------------

context
  choose x_def: 'x' 
    let 'y'
    let 'x = y'
  show x_def
  assert (x_def : Term) == '∀ y. x y = y'

# the same as above, but using an intermediate theorem
context
  theorem t: '∀ y ∃ x. x = y'
    let 'y'
    let 'x = y'    
  choose x_def: 'x' t
  show x_def
  assert (x_def : Term) == '∀ y. x y = y'

# we can move the intermediate theorem into choose
context
  choose x_def: 'x : 𝒰 → _'
    theorem '∀ y ∃ x. x = y'
      let 'y'
      let 'x = y'
  show x_def
  assert (x_def : Term) == '∀ y. x y = y'

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
  assert (trivial : Term) == '∀ p. p → p'
  assert w == 2

# theorems without explicitly stating the proposition
context 
  theorem t: nil
    let 'p : ℙ'
    assume p: 'p'
    let 'a'
    p
  assert (t : Term) == '∀ p. p → p'
  theorem  
    let 'p : ℙ'
    assume p: 'p'
    let 'a'
    p
  assert (t : Term) == '∀ p. p → p'
  theorem t: nil!
    let 'p : ℙ'
    assume p: 'p'
    let 'a'
    p
  assert (t : Term) == '∀ p. p → (∀ a. p)'

# context, literalcontext, incontext, inliteralcontext
  ----------------------------------------------------

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

context
  val tm = '∀ p. p → p'
  def prf() =
    let p: 'p : ℙ'
    assume prop: p
    prop
  theorem t: tm
    prf()

context
  val tm = '∀ p. p → p'
  def prf() =
    let 'p : ℙ'
    assume prop: 'p'
    prop
  failure
    theorem t: tm
      prf()

context
  val tm = '∀ p. p → p'
  def prf() =
    inliteralcontext
      let 'p : ℙ'
      assume prop: 'p'
      prop
  theorem t: tm
    prf()

context
  val tm = '∀ p. p → p'
  def prf() =
    let 'p : ℙ'
    assume prop: (inliteralcontext<context> 'p')
    prop
  theorem t: tm
    prf()

context
  let 'p'
  def f () = ('p', 'q')
  def g c =
    inliteralcontext<c> 
      ('p', 'q')
  let 'q'
  failure f()
  assert g (context) == ('p', 'q')
  assert g literalcontext == ('p', 'q')

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

show  context
