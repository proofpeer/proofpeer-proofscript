theory \issue30 extends \root

context
  let 'f:𝒰'
  let 'x:𝒰'
  val foo = 
    match 'f x'
      case '‹rat› ‹rand›' => true
      case _              => false
  assert foo

context
  let 'f:𝒰 → 𝒰'
  let 'x:𝒰'
  val foo = 
    match 'f x'
      case '(‹rat› : _ → _) ‹rand›' => true
      case _ => false
  assert foo