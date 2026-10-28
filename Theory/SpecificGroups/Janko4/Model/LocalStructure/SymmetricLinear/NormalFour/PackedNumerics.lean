module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Data

/-!
# Checked cyclic rows and annihilator coefficients

Source: ATLAS `J4G1-f2r112B0` and `J4G1-max4W1`, as attributed in
`Model/Data.lean` and `SymmetricLinear/Model.lean`. Reproduce using
`NormalFour/source/generate.py`. All numerical equalities are kernel checked.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
open GeneratorCertificates Simplicity.Elevens.BridgeCertificate Matrix

set_option maxRecDepth 10000

theorem cyclic_rows_packed : ∀ i : Fin 112, qRows.get i = (wordRows.get i).get 0 := by decide +kernel

theorem polynomial_packed : ∀ i : Fin 112,
    xorList (polynomialRows.map (fun v => v.get i)) = rRows.get i := by decide +kernel

theorem projection_packed : ∀ i : Fin 112,
    pRows.get i = 2 ^ i.val ^^^
      ((if i = 0 then 1 else 0) ^^^ (if i = 1 then 2937915053987813481625123188289954 else 0)) := by decide +kernel

theorem annihilator_zero_row_packed : rRows.get 0 = 0 := by decide +kernel

end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
