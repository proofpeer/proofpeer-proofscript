theory issue34 extends \root

val [ctx,x,bod]  = destabs 'x ↦ x'
val [ctx2,y,bod] = destabs 'y ↦ y'
context <ctx2>
  show x
  show y
