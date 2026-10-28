module

public import Theory.SpecificGroups.Thompson.Model.Order.Cosets.Separation.RowWords

/-!
# The three nonzero rows of a candidate binary plane

The two packed rows were found by GAP's MeatAxe on the precise local subgroup
words. They are candidate data; their invariance is proved in the neighboring
modules. Source data and attribution: `Model/source/README.md` and
`Order/source/README.md`. The certificate producer is `Separation/source/generate.py`.
-/

namespace Thompson.OrderCertificate.Separation

@[expose] public def fixedRow0 : Fin 248 → ZMod 2 := row 295297160020848316126516621986431863927811240817991627874462457367798847899

@[expose] public def fixedRow1 : Fin 248 → ZMod 2 := row 53118203310247861616881865655955129280624587562044029180903589568007838922

@[expose] public def fixedRow2 : Fin 248 → ZMod 2 := fixedRow0 + fixedRow1

public theorem row_xor (r s : ℕ) : row (r ^^^ s) = row r + row s := by
  funext j
  exact BinaryMatrix.bit_xor r s j.val

end Thompson.OrderCertificate.Separation
