theory issue31 extends \root

# Temporarily removed feature from language which allows introduction of variables via quotes

# context
  val x
  let '‹x›'
  show x

# val foo = _ =>
    context
      let x:'‹x›'
      show x