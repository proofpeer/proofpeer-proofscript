theory issue55 extends \root

context
  let one: 'one = 𝒫 ∅'
  val x =  
      '(((((∀ x. ¬ (x ∈ ∅)) ∧ (one = (𝒫 ∅))) ∧ (∀ x. ∀ y. ((x ∈ (𝒫 y)) ∨ (¬ (x ⊂ y))) ∧ ((¬ (x ∈ (𝒫 y))) ∨ (x ⊂ y)))) ∧ (∀ x. ∀ y. ((x ⊂ y) ∨ (¬ (∀ z ∈ x. z ∈ y))) ∧ ((¬ (x ⊂ y)) ∨ (∀ z ∈ x. z ∈ y)))) ∧ (∀ x_4. ∀ y_1. ((x_4 = y_1) ∨ (∃ x_2. ¬ ((x_1 ↦ (x_1 ∈ x_4) = (x_1 ∈ y_1)) x_2))) ∧ ((¬ (x_4 = y_1)) ∨ (∀ z. ((z ∈ x_4) ∨ (¬ (z ∈ y_1))) ∧ ((¬ (z ∈ x_4)) ∨ (z ∈ y_1)))))) ∧ (∃ x_2. ¬ ((x_1 ↦ (x_1 ∈ one) = (x_1 = ∅)) x_2))'      
  val y =  
      '∀ x_6. ∀ x_5. ∃ x_3. ∃ y. ∀ x. ((x_2 ↦ (((¬ ((x_3 ∈ x_6) = (x_3 ∈ x_5))) ∨ (x_6 = x_5)) ∧ ((((x_2 ∈ x_6) ∨ (¬ (x_2 ∈ x_5))) ∧ ((¬ (x_2 ∈ x_6)) ∨ (x_2 ∈ x_5))) ∨ (¬ (x_6 = x_5)))) ∧ (((((x_6 ∈ (𝒫 x_5)) ∨ (¬ (x_6 ⊂ x_5))) ∧ ((¬ (x_6 ∈ (𝒫 x_5))) ∨ (x_6 ⊂ x_5))) ∧ ((¬ (x_6 ∈ ∅)) ∧ (one = (𝒫 ∅)))) ∧ (((x_6 ⊂ x_5) ∨ (¬ (∀ z ∈ x_6. z ∈ x_5))) ∧ ((¬ (x_6 ⊂ x_5)) ∨ (∀ z ∈ x_6. z ∈ x_5))))) x) ∧ ((x ↦ ¬ ((y ∈ one) = (y = ∅))) x)'
  val t = 
      '((((((∀ x. ¬ (x ∈ ∅)) ∧ (one = (𝒫 ∅))) ∧ (∀ x. ∀ y. ((x ∈ (𝒫 y)) ∨ (¬ (x ⊂ y))) ∧ ((¬ (x ∈ (𝒫 y))) ∨ (x ⊂ y)))) ∧ (∀ x. ∀ y. ((x ⊂ y) ∨ (¬ (∀ z ∈ x. z ∈ y))) ∧ ((¬ (x ⊂ y)) ∨ (∀ z ∈ x. z ∈ y)))) ∧ (∀ x_4. ∀ y_1. ((x_4 = y_1) ∨ (∃ x_2. ¬ ((x_1 ↦ (x_1 ∈ x_4) = (x_1 ∈ y_1)) x_2))) ∧ ((¬ (x_4 = y_1)) ∨ (∀ z. ((z ∈ x_4) ∨ (¬ (z ∈ y_1))) ∧ ((¬ (z ∈ x_4)) ∨ (z ∈ y_1)))))) ∧ (∃ x_2. ¬ ((x_1 ↦ (x_1 ∈ one) = (x_1 = ∅)) x_2))) = (∀ x_6. ∀ x_5. ∃ x_3. ∃ y. ∀ x. ((x_2 ↦ (((¬ ((x_3 ∈ x_6) = (x_3 ∈ x_5))) ∨ (x_6 = x_5)) ∧ ((((x_2 ∈ x_6) ∨ (¬ (x_2 ∈ x_5))) ∧ ((¬ (x_2 ∈ x_6)) ∨ (x_2 ∈ x_5))) ∨ (¬ (x_6 = x_5)))) ∧ (((((x_6 ∈ (𝒫 x_5)) ∨ (¬ (x_6 ⊂ x_5))) ∧ ((¬ (x_6 ∈ (𝒫 x_5))) ∨ (x_6 ⊂ x_5))) ∧ ((¬ (x_6 ∈ ∅)) ∧ (one = (𝒫 ∅)))) ∧ (((x_6 ⊂ x_5) ∨ (¬ (∀ z ∈ x_6. z ∈ x_5))) ∧ ((¬ (x_6 ⊂ x_5)) ∨ (∀ z ∈ x_6. z ∈ x_5))))) x) ∧ ((x ↦ ¬ ((y ∈ one) = (y = ∅))) x))'
  assume th: t
  timeit
    val s 
    timeit
      s = '‹x› = ‹y›'
    timeit
      theorem foo: s
        th
      foo

# The timings resulting for this code before dealing with this issue are:

  start compiling theory '\issues\issue55' ...
    ** timeit (\issues\issue55:14): 462ms
    ** timeit (\issues\issue55:16): 9ms
    ** timeit (\issues\issue55:12): 475ms
  successfully compiled theory '\issues\issue55'

