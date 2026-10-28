module

public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure

/-!
# The outer-order bound in arbitrary four-element coordinates

Entrywise field transport identifies PSL₃ over the given field with the
existing four-element model. Transport of Aut/Inn then gives the proved
outer-order bound. A consumer can keep its original quotient marking: the
comparison is used only to compute a cardinality.

Source: GLS3, Theorem 2.5.12 and Section 2.7; used in Aschbacher--Smith,
proof of 15.3.38, printed p.1136. The imported ATLAS field transport retains
its attribution and license in `ExceptionalIsomorphisms.Support`.
-/

public section
open scoped MatrixGroups
namespace Matrix.PSL3Four.OuterThreeStructure

/-- The literal outer group has order dividing twelve over any four-element field. -/
theorem outer_card_dvd_twelve_of_card_four {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 4) : Nat.card (MulAut.Outer PSL(3,K)) ∣ 12 := by
  let := Fintype.ofFinite K
  let := Fintype.ofFinite F
  let eF : K ≃+* F := FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, card_F])
  rw [Nat.card_congr (MulAut.outerCongr (Atlas.fieldEquivPSL 3 eF)).toEquiv]
  exact outer_card_dvd_twelve

end Matrix.PSL3Four.OuterThreeStructure
