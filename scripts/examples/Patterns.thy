theory Patterns extends \root

def 
  f 0 = true
  f [1, 2, 7] = true
  f "hello" = true
  f false = true
  f _ = false

assert f 0
assert not f 1
assert f [1, 2, 7]
assert f "hello"
assert not f "hello world"
assert f false
assert not f true

def 
  sum [] = 0
  sum x <+ xs = x + sum xs

def
  fibPrefix [] = true
  fibPrefix [0] = true
  fibPrefix [0, 1] = true
  fibPrefix xs +> x +> y +> z = 
    fibPrefix (xs +> x +> y) and z == x + y

assert fibPrefix []
assert fibPrefix [0]
assert fibPrefix [0, 1]
assert fibPrefix [0, 1, 1]
assert fibPrefix [0, 1, 1, 2]
assert fibPrefix [0, 1, 1, 2, 3]
assert fibPrefix [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]
assert not fibPrefix [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 56, 89]

def 
  g [] = true
  g xs +> x if g xs = 
    size xs == x

assert g []
assert g [0]
assert g [0, 1]
assert g [0, 1, 2]
assert g [0, 1, 2, 3]
assert not g [0, 1, 2, 3, 5]

def 
  brackets [] = true
  brackets "(" <+ s +> ")" = brackets s
  brackets _ = false

assert brackets []
assert brackets ["(", ")"]
assert brackets ["(","(",")",")"]
assert brackets ["(", "(", "(", "(", ")", ")", ")", ")"]
assert not brackets ["(", "(", ")"]

def 
  even x if x mod 2 == 0 = true
  even x if x mod 2 == 1 = false
  even _ = fail "unexpected case in even"

assert even 10
assert not even 11
assert even (-10)
failure even (-11)

def 
  duphead x <+ _ as xs = x <+ xs
  duphead xs = xs

assert duphead [] == []
assert duphead [1, 2, 3] == [1, 1, 2, 3]

do
  val x = 10
  def tricky ((y if y == x) <+ _ as x) = x
  assert tricky [10] == [10]
  failure tricky [11]

# Let's do some term matching

def 
  polyAll '∀ x. x = x' = true
  polyAll _ = false

def monoAll t = t == '∀ x. x = x'

val sUniv = '∀ x : 𝒰. x = x'
val sProp = '∀ x : ℙ. x = x'

assert polyAll sUniv and polyAll sProp
assert monoAll sUniv
assert not monoAll sProp

let 'x : 𝒰'
let 'y : ℙ'
choose inf: 'inf' infinity

def 
  dest t =
    match t
      case '‹p› ∧ ‹q›' => (1, p, q)
      case '∃ X. ‹p› X ∧ ‹q› X' => (2, p, q)
      case '‹p› = ‹q›' => (3, p, q)
      case '∀ x. ‹p› x = ‹q› x' => (4, p, q)
      case _ => nil  

assert dest inf == [1, '∅ ∈ inf', '∀ x ∈ inf. x ∪ {x} ∈ inf']
assert dest infinity == [2, 'X ↦ ∅ ∈ X', 'X ↦ ∀ x ∈ X. x ∪ {x} ∈ X']
assert dest 'x = x' == [3, 'x', 'x']
assert dest '∀ q. q = x' == [4, 'y ↦ y', 'y ↦ x']
assert dest '∀ q. q = y' == [4, 'x : ℙ ↦ x', 'x : ℙ ↦ y']
assert dest '∃ q. q = x' == nil

# Pattern matching based on type of value

def typeOf v =
  match v
    case _ : Nil => "Nil"
    case _ : Boolean => "Boolean"
    case _ : Integer => "Integer"
    case _ : String => "String"
    case _ : Tuple => "Tuple"
    case _ : Map => "Map"
    case _ : Set => "Set"
    case _ : Term => "Term"
    case _ : Type => "Type"
    case _ : Theorem => "Theorem"
    case _ : Context => "Context"
    case _ : Function => "Function"
    case _ : _ => "Any"

def check (v, ty : String) = 
  assert typeOf v == ty
  ()

_ = (do*
  check ('x', "Term")
  check (1, "Integer")
  check (nil, "Nil")
  check (true, "Boolean")
  check ((1), "Integer")
  check ((1, 2), "Tuple")
  check ([1], "Tuple")
  check (': 𝒰', "Type")
  check (inf, "Theorem")
  check ({1}, "Set")
  check ({1 -> 1}, "Map")
  check ((context), "Context")
  check ("check", "String")
  check (x => x, "Function"))

def f (x : Integer) : Integer = if x == 0 then "0" else (x * x : Integer)

assert f 12 == 144
failure f "12"
failure f 0

def g (x : Integer) : Integer? = if x == 0 then nil else x * x
assert g 0 == nil
assert g 12 == 144

def h x : Integer | String = if x == 0 then "0" else x

assert h 0 == "0"
assert h 1 == 1
assert h "hello" == "hello"
failure h ': 𝒰'



