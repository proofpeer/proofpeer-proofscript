theory Redundancies
extends Metis

# Useful for certain redudancies.
choose anonymous: 'anonymous: 𝒰'
  let x:'x'
  let 'y = x'
  reflexive 'y'

choose oneDef: 'one:𝒰'
  let one:'one = 𝒫 ∅'
  theorem '∀x. x ∈ one = (x = ∅)'
    by metis [empty,one,power,subset,ext]

choose twoDef: 'two:𝒰'
  let two:'two = 𝒫 one'
  theorem '∀x. x ∈ two = (x = ∅ ∨ x = one)'
    by metis [empty,oneDef,two,power,subset,ext]
