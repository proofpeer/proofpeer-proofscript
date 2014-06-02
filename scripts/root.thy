theory root 
extends

assume trueDef = '((p : ℙ ↦ p) = (p : ℙ ↦ p))'
assume falseDef = '⊥ = (∀ p. p)'
assume notDef = '∀ p. (¬ p) = (p → ⊥)'
assume andDef = '∀ x, y. (x ∧ y) = ((f ↦ f x y) = (f ↦ f ⊤ ⊤))'
assume impliesDef = '∀ x, y. (x → y) = ((x ∧ y) = x)'
assume orDef = '∀ x, y. (x ∨ y) = (∀ z. (x → z) → (y → z) → z)'
assume empty = '∀ x. x ∉ ∅'
assume ext = '∀ x, y. (x = y) = (∀ z. z ∈ x = z ∈ y)'
assume Union = '∀ z, x. z ∈ ⋃ x = (∃ y ∈ x. z ∈ y)'
assume union = '∀ x, y, z. (z ∈ x ∪ y) = (z ∈ x ∨ z ∈ y)'
assume Intersection = '∀ z, x. z ∈ ⋂ x = (∀ y ∈ x. z ∈ y)'
assume intersection = '∀ x, y, z. z ∈ x ∩ y = (z ∈ x ∧ z ∈ y)'
assume difference = '∀ x, y, z. z ∈ x ∖ y = (z ∈ x ∧ z ∉ y)'
assume subset = '∀ x, y. x ⊂ y = (∀ z ∈ x. z ∈ y)'
assume singleton = '∀ x, y. y ∈ {x} = (y = x)'
assume power = '∀ x, y. x ∈ 𝒫 y = x ⊂ y'
assume repl = '∀ A, f, b. b ∈ repl A f = (∃ a ∈ A. b = f a)'
assume sep = '∀ A, p, a. a ∈ sep A p = (a ∈ A ∧ p a)'
assume regularity = '∀ A. A ≠ ∅ → (∃ x ∈ A. x ∩ A = ∅)'
assume infinity = '∃ X. ∅ ∈ X ∧ (∀ x ∈ X. x ∪ {x} ∈ X)'
assume forallin = '∀ X, P. forallin X P = (∀ x. x ∈ X → P x)'
assume existsin = '∀ X, P. existsin X P = (∃ x. x ∈ X ∧ P x)'
assume pair = '∀ x, y. (x, y) = {{x}, {x, y}}'
assume fun = '∀ X, f. fun X f = {(x, f x)| x ∈ X}'
assume apply = '∀ X, f, x ∈ X. fun X f x = f x'

show 1

val x = 10
val y = 20

show x
show regularity
show context
