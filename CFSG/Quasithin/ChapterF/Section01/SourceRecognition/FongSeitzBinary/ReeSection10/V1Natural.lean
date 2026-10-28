module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.V1Faithfulness
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.LinearNatural

/-!
# The faithful natural action on the literal linear section

The actual V₁=U_s₁/X₁ has binary dimension 2(2m+1), and its previously
proved faithful rank-one action is therefore irreducible and natural.
The chosen intertwiner uses the same field as the Suzuki layers and the
whole linear pinning aligned with the supplied reflection. Its formula
on quotient representatives is actual conjugation. Every parameter,
including m=0, is retained.

This discharges the natural-action step before (10.6), without assuming
it in ReeSixHData. Aligning these coordinates with the two printed root
vectors, synchronizing field labels, and deriving the mixed equations
remain separate steps. Source: Fong--Seitz II, pp.222--223.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

local instance v1NaturalBinaryAlgebra : Algebra (ZMod 2) (ReeF4.CoefficientField m) := ZMod.algebra _ 2

theorem linearV1_irreducible : (linearV1Representation Q split c).IsIrreducible :=
  linear_minimal_irreducible _ (linearV1Representation_injective Q split c)
    (2*m+1) (by omega) (GaloisField.card 2 (2*m+1) (by omega)) (V1_finrank Q split c)

theorem V1_irreducible : (V1Representation Q split c).IsIrreducible :=
  (Representation.irreducible_comp_surjective_iff (linearPinning Q split c).toMonoidHom
    (linearPinning Q split c).surjective (V1Representation Q split c)).mp
      (linearV1_irreducible Q split c)

/-- The whole literal quotient is the natural module, including q=2. -/
theorem V1_natural : Nonempty ((linearV1Representation Q split c).Equiv
    (Representation.SL2.BinarySmall.natural (K := ReeF4.CoefficientField m))) :=
  linear_minimal_natural _ (linearV1Representation_injective Q split c)
    (2*m+1) ⟨m,rfl⟩ (GaloisField.card 2 (2*m+1) (by omega)) (V1_finrank Q split c)

/-- Natural coordinates, before alignment with the printed basis (10.6). -/
def V1Coordinates : (linearV1Representation Q split c).Equiv
    (Representation.SL2.BinarySmall.natural (K := ReeF4.CoefficientField m)) :=
  (V1_natural Q split c).some

theorem V1Coordinates_source (r : rankOne Q split 0) (v : (V1Section Q split c).numerator) :
    V1Coordinates Q split c (Additive.ofMul (QuotientGroup.mk
      ((V1Section Q split c).numeratorAction r v))) =
      Representation.SL2.BinarySmall.natural ((linearPinning Q split c).symm r)
        (V1Coordinates Q split c (Additive.ofMul (QuotientGroup.mk v))) := by
  have he := LinearMap.congr_fun ((V1Coordinates Q split c).isIntertwining'
    ((linearPinning Q split c).symm r)) (Additive.ofMul (QuotientGroup.mk v))
  change V1Coordinates Q split c
    (V1Representation Q split c ((linearPinning Q split c) ((linearPinning Q split c).symm r))
      (Additive.ofMul (QuotientGroup.mk v))) = _ at he
  rw [MulEquiv.apply_symm_apply] at he
  exact he

/-- The supplied reflection has the natural Weyl matrix on this very quotient. -/
theorem V1Coordinates_reflection (v : (V1Section Q split c).numerator) :
    V1Coordinates Q split c (Additive.ofMul (QuotientGroup.mk
      ((V1Section Q split c).numeratorAction
        ⟨(c.reflections 0).val,(c.reflections 0).mem_rankOne⟩ v))) =
      Representation.SL2.BinarySmall.natural (Theory.PSL2.SemilinearCoverage.weyl _)
        (V1Coordinates Q split c (Additive.ofMul (QuotientGroup.mk v))) := by
  have hr : (⟨(c.reflections 0).val,(c.reflections 0).mem_rankOne⟩ : rankOne Q split 0) =
      linearPinning Q split c (Theory.PSL2.SemilinearCoverage.weyl _) :=
    Subtype.ext (linearPinning_weyl Q split c).symm
  rw [V1Coordinates_source,hr,MulEquiv.symm_apply_apply]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
