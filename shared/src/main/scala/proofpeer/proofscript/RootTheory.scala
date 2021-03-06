package proofpeer.proofscript

object RootTheory {

  val thy = """theory root 

val versionOfProofScript = """" + ProofScriptManager.currentVersion + """"

let trueDef: 'true = ((p : ℙ ↦ p) = (p ↦ p))'
let falseDef: 'false = (∀ p. p)'
let andDef: 'and = (x y ↦ ((f ↦ (f x y) : ℙ) = (f ↦ f ⊤ ⊤)))'
let notDef: 'not = (p ↦ (p → ⊥))'
let orDef: 'or = (x y ↦ (∀ z. (x → z) → (y → z) → z))'

let 'empty'
let 'difference : 𝒰 → 𝒰 → 𝒰'
let 'union : 𝒰 → 𝒰 → 𝒰'
let 'Union : 𝒰 → 𝒰'
let 'intersection : 𝒰 → 𝒰 → 𝒰'
let 'Intersection : 𝒰 → 𝒰'
let 'power : 𝒰 → 𝒰'
let 'singleton : 𝒰 → 𝒰'
let 'sep : 𝒰 → (𝒰 → ℙ) → 𝒰'
let 'repl : 𝒰 → (𝒰 → 𝒰) → 𝒰'
let 'elementof : 𝒰 → 𝒰 → ℙ'
let 'subsetof : 𝒰 → 𝒰 → ℙ'
let 'pair : 𝒰 → 𝒰 → 𝒰'
let 'fun : 𝒰 → (𝒰 → 𝒰) → 𝒰'
let 'apply : 𝒰 → 𝒰 → 𝒰'
let 'forallin : 𝒰 → (𝒰 → ℙ) → ℙ'
let 'existsin : 𝒰 → (𝒰 → ℙ) → ℙ'

assume empty: '∀ x. x ∉ ∅'
assume ext: '∀ x, y. (x = y) = (∀ z. z ∈ x = z ∈ y)'
assume bigUnion: '∀ z, x. z ∈ ⋃ x = (∃ y ∈ x. z ∈ y)'
assume union: '∀ x, y, z. (z ∈ x ∪ y) = (z ∈ x ∨ z ∈ y)'
assume bigIntersection: '∀ z, x. x ≠ ∅ → z ∈ ⋂ x = (∀ y ∈ x. z ∈ y)'
assume intersection: '∀ x, y, z. z ∈ x ∩ y = (z ∈ x ∧ z ∈ y)'
assume difference: '∀ x, y, z. z ∈ x ∖ y = (z ∈ x ∧ z ∉ y)'
assume subset: '∀ x, y. x ⊂ y = (∀ z ∈ x. z ∈ y)'
assume singleton: '∀ x, y. y ∈ {x} = (y = x)'
assume power: '∀ x, y. x ∈ 𝒫 y = x ⊂ y'
assume repl: '∀ A, f, b. b ∈ repl A f = (∃ a ∈ A. b = f a)'
assume sep: '∀ A, p, a. a ∈ sep A p = (a ∈ A ∧ p a)'
assume regularity: '∀ A. A ≠ ∅ → (∃ x ∈ A. x ∩ A = ∅)'
assume infinity: '∃ X. ∅ ∈ X ∧ (∀ x ∈ X. x ∪ {x} ∈ X)'
assume forallin: '∀ X, P. forallin X P = (∀ x. x ∈ X → P x)'
assume existsin: '∀ X, P. existsin X P = (∃ x. x ∈ X ∧ P x)'
assume pair: '∀ x, y. (x, y) = {{x}, {x, y}}'
assume fun: '∀ X, f. fun X f = {(x, f x)| x ∈ X}'
assume apply: '∀ X, f, x ∈ X. fun X f x = f x'
"""

}