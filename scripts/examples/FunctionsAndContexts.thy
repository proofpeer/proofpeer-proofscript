theory FunctionsAndContexts extends \root

# Block A
def 
  dest t =
    match t
      case '‹p› ∧ ‹q›' => (1, p, q)
      case '∃ X. ‹p› X ∧ ‹q› X' => (2, p, q)
      case '‹p› = ‹q›' => (3, p, q)
      case '∀ x. ‹p› x = ‹q› x' => (4, p, q)
      case _ => nil  

# Block B
let 'x : 𝒰'
let 'y : ℙ'
choose inf: 'inf' infinity

# Block C
assert dest inf == [1, '∅ ∈ inf', '∀ x ∈ inf. x ∪ {x} ∈ inf']
assert dest infinity == [2, 'X ↦ ∅ ∈ X', 'X ↦ ∀ x ∈ X. x ∪ {x} ∈ X']
assert dest 'x = x' == [3, 'x', 'x']
assert dest '∀ q. q = x' == [4, 'y ↦ y', 'y ↦ x']
assert dest '∀ q. q = y' == [4, 'x : ℙ ↦ x', 'x : ℙ ↦ y']
assert dest '∃ q. q = x' == nil