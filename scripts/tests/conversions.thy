theory ConversionTests
extends root Conversions List

assert map (term,absConv (tm => [reflexive tm]) 'x ↦ ⊤') == ['(x ↦ ⊤) = (x ↦ ⊤)']

assert map (term,absConv idConv 'x ↦ ⊤') == ['(x ↦ ⊤) = (x ↦ ⊤)']

assert map (term,absConv (subsConv [reflexive '⊤']) 'x ↦ ⊤') == ['(x ↦ ⊤) = (x ↦ ⊤)']
