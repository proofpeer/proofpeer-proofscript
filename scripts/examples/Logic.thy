theory Logic extends \root

# term
  ------------------------------------

context
  let 'x'
  assert ('x' : Term) == 'x'
  assert ("x" : Term) == 'x'
  assume x: 'x = x'
  assert (x : Term) == 'x = x'
  
context
  let 'x'
  val t
  context
    let 'y' 
    t = assume 'x = y'
    assert (t : Term) == 'x = y'
  assert (t : Term) == '∀ y. x = y → x = y'


# fresh
  ------------------------------------

context
  failure term (fresh "x")
  theorem t: '∀ a b c p. p → p'
    let (fresh "x")
    let (fresh "x")
    let (fresh "x")
    let p: '‹fresh "p"› : ℙ'
    assert p == 'p : ℙ'
    assume p
  show t
  assert fresh "x" == fresh "x"
  assert (fresh "x" : String) == fresh "x"

# context
  theorem t: '∀ a b c p. p → p'
    let '‹a›'
    let '‹b›'
    let '‹c›'
    failure p
    let '‹p› : ℙ'
    assert p == "p"
    assume '‹p›'
  show t

# context
  let 'p'
  theorem t: '∀ a b c p. p → p'
    let '‹a›'
    let '‹b›'
    let '‹c›'
    failure p
    let '‹p› : ℙ'
    assert p <> "p"
    assume '‹p›'
  show t


# string
  ------------------------------------

context
  let 'x'
  assert ('x' : String) == "x"
  assert ("x" : String) == "x"
  assume x: 'x = x'
  assert (x : String) == "x = x"


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


# modusponens
  ------------------------------------

context
  let 'x1 : ℙ'
  let 'x2 : ℙ'
  let 'x3 : ℙ'
  let 'x4 : ℙ'
  assume t12: 'x1 = x2'
  assume t23: 'x2 → x3'
  assume t34: 'x3 = x4'
  theorem t14: 'x1 → x4'
    assume t1: 'x1'
    modusponens (t1, t12, t23, t34)
  theorem 'x1 = x2'
    modusponens [t12]
  failure modusponens []
  failure modusponens t12


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

# normalize
  ------------------------------------

context
  let 'Q : 𝒰 → ℙ'
  val u = '(P ↦ (x ↦ P x)) Q'
  theorem t: '‹u› = Q'
    reflexive 'Q'
  assert (t : Term) == (normalize u : Term)


# equivalence
  ------------------------------------

context
  let 'p : ℙ'
  let 'q : ℙ'
  assume u: 'p → q'
  assume v: 'q → p'
  theorem 'p = q'
    equivalence(u, v)


# abstract
  ------------------------------------

context
  let 'f'
  let 'g'
  assume t: '∀ x. f x = g x'
  theorem '(x ↦ f x) = (x ↦ g x)'
    abstract t

# instantiate
  ------------------------------------

context
  let 'P : 𝒰 → 𝒰 → 𝒰 → ℙ'
  assume t: '∀ x y z. P x y z'
  let 'a'
  let 'b'
  let 'c'
  theorem 'P a b c'
    instantiate (t, 'a', 'b', 'c')
  theorem 'P b c a'
    instantiate (t, 'b', 'c', 'a')
  failure instantiate []
  failure instantiate t
  theorem (t : Term) 
    instantiate [t]
  theorem '∀ y z. P a y z'
    instantiate (t, 'a')
  theorem '∀ z. P a b z'
    instantiate (t, 'a', 'b')
  theorem '∀ x z. P x b z'
    instantiate (t, , 'b', nil)
  theorem '∀ y. P a y b'
    instantiate (t, 'a', nil, 'b')    
  theorem (t : Term) 
    instantiate [t, , nil, nil]

# destcomb
  ------------------------------------

context
  let 'f : 𝒰 → 𝒰'
  let 'x : 𝒰'
  val (u, v) = destcomb 'f x'
  assert u == 'f'
  assert v == 'x'
  assert destcomb 'f' == nil

context
  let 'x'
  val (eq, right) = destcomb (normalize '(x ↦ x) x' : Term)
  val (_, left) = destcomb eq
  assert left == right
  assert destcomb left <> destcomb right
  assert destcomb left == ('x ↦ x', 'x')
  assert destcomb right == nil

# destabs
  ------------------------------------
  
context  
  let 'f : 𝒰 → 𝒰'
  assert destabs 'f' == nil
  val (ctx, x, body) = destabs 'k ↦ f k'
  context <ctx>
    assert x == 'k'
    assert body == 'f k'
    assert body == 'f ‹x›'


