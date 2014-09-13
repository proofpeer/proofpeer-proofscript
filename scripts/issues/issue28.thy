theory \issue28 extends \root

context
  let 'x'
  val [u, v] =
    match normalize '(x ↦ x) x'
      case '‹u› = ‹v›' => [u, v]
  assert u == '(x ↦ x) x'
  assert v == 'x'

context
  let 'f : ℙ → ℙ'
  match 'forall f'
    case '∀ x. ‹P› x' =>
      assert P == 'f'
  match '∀ y. f y'
    case '∀ x. ‹P› x' =>
      assert P == 'f'

