module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining.Bridge
/-!
# Certified dense row of both degree-1000 intertwining identities

The actual source lift numbered 840 has 828 nonzero ambient coefficients.
Both complete packed products are kernel-checked and transported through the
proved ambient and lift alignments to the literal matrix rows. These theorems
can be reused in the full 1000-row families; they alone do not prove invariance.

Source: R. A. Wilson et al., ATLAS HSG1-f2r56B0/HSG1-f2r1000B0 and
`Binary/source/section1000.json`. Attribution and rights are retained in
`Binary/source/README.md`; measurements are in `Intertwining/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining

theorem packed_a_row840 : Tables.a.product liftRows[840]! =
    Tables.lifts.product D1000.aRows[840]! := by decide +kernel

theorem packed_b_row840 : Tables.b.product liftRows[840]! =
    Tables.lifts.product D1000.bRows[840]! := by decide +kernel

theorem u_mul_ambientA_row840 : (U * ambientA) ⟨840, by decide⟩ =
    (targetA * U) ⟨840, by decide⟩ := rowA_of_product ⟨840, by decide⟩ packed_a_row840

theorem u_mul_ambientB_row840 : (U * ambientB) ⟨840, by decide⟩ =
    (targetB * U) ⟨840, by decide⟩ := rowB_of_product ⟨840, by decide⟩ packed_b_row840

end Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining
