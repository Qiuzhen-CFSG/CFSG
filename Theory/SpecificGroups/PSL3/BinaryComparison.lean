module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The binary degree-three projective group

Field transport extends the existing faithful-action isomorphism
`PSL₂(7) ≃ PSL₃(2)` to any two-element coefficient field. This separates
the binary endpoint from the ordinary degree-three covering calculations in
Aschbacher–Smith I.1.3, printed p.407.

The imported isomorphism is the attributed ATLAS port in
`Theory.AtlasPort.ExceptionalIsomorphisms.Order168`; its source attribution
and ATLAS Research and Attribution License 1.0 notice are retained there.
-/

namespace Matrix.PSL3

open scoped MatrixGroups

/-- The actual degree-three group over any two-element field is `PSL₂(7)`. -/
public noncomputable def binaryEquivPsl2Seven
    (F : Type*) [Field F] [Finite F] (hF : Nat.card F = 2) :
    PSL(3, F) ≃* PSL(2, ZMod 7) := by
  letI : Fintype F := Fintype.ofFinite F
  let e : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact (Atlas.fieldEquivPSL 3 e).trans
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm

end Matrix.PSL3
