theory Redundancies
extends Metis

# Useful for certain redudancies.
choose anonymous: 'anonymous: 𝒰'
  let x:'x'
  let 'y = x'
  reflexive 'y'

let oneDef:'one = 𝒫 ∅'
let twoDef:'two = 𝒫 one'

theorem one:'∀x. x ∈ one = (x = ∅)'
  by metis [empty,oneDef,power,subset,ext]

theorem two:'∀x. x ∈ two = (x = ∅ ∨ x = one)'
  by metis [empty,one,twoDef,power,subset,ext]

theorem oneNotZero: '¬(∅ = one)'
  by metis [empty, one]