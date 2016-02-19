theory Logic2 
  Logic2Alias = Logic
  Logic2Alias2 = Logic2
extends Logic

show sin
show '\examples\Logic\sin'

assert sin == 'Logic\sin'

val message2 = "This is a message in Logic2."

show testProgramNamespace()
failure show testProgramNamespace2()

failure show Logic2\message2

