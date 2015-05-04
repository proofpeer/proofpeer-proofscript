theory issue57 extends \root

def mkabs (ty, f) =
  theorem eq: true
    val x = fresh "x"
    let x: '‹x› : ‹ty›'
    reflexive (f x)
  match eq
    case '∀ x. ‹u› x = ‹v› x' => u

assert mkabs(':𝒰', u => mkabs (':ℙ', x => '‹x› ∨ (¬‹x›)')) == 'u ↦ x ↦ x ∨ (¬x)'

