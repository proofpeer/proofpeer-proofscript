theory Logic2 
  Logic2Alias = Logic
  Logic2Alias2 = Logic2
extends Logic

show sin
show '\examples\Logic\sin'
failure '\examples\Logic2\sin'

assert sin == 'Logic\sin'

val message2 = "This is a message in Logic2!"

failure testProgramNamespace()
failure testProgramNamespace2()

show Logic\message
failure Logic2\message2
failure Logic2\message

