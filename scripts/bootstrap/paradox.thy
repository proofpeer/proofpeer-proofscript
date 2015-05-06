theory Paradox
extends Metis

let universeDef: 'universe = ⋂ ∅'

theorem universe:'∀x. x ∈ universe'
  by metis (universeDef, empty, Intersection)

theorem paradox:'⊥'
  by metis (instantiate [sep, 'universe', 'x ↦ ¬(x ∈ x)'], universe)

show paradox