theory \issue28 extends \root

context
  let 'x'
  val [u, v] =
    match normalize '(x ↦ x) x'
      case '‹u› = ‹v›' => [u, v]
  assert u == '(x ↦ x) x'
  assert v == 'x'
