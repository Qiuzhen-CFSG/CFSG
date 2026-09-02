module
#synth Subsingleton Prop
#check Subsingleton.elim (α := Prop)
example (P Q : Prop) : P = Q := by exact Subsingleton.elim _ _
