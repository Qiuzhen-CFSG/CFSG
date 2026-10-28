module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.NaturalAlignment
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.NaturalLayers

/-!
# Choice independence for the two Section 10 natural coordinates

The source construction chooses one natural-module intertwiner on each of the
literal V₂ and Φ(V)/Z(V) representations.  This leaf records the exact
freedom in those choices: any second choice differs by one nonzero scalar on
the same natural module.  Thus later root-line and coefficient normalizations
may impose one scalar convention without changing the source action or its
literal quotient.  The statement is conditional on the proved Section 10
input and includes `m = 0`.

Source: Fong--Seitz II (1974), equations (10.7)--(10.9), with the scalar
centralizer calculation on the natural Suzuki module.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups Representation
open scoped IsMulCommutative
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

open ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

include c in
/-- Any two choices of the V₂ natural coordinates differ by one nonzero field
scalar. -/
theorem V2Coordinates_choice_scalar
    (e₁ e₂ : (suzukiV2Representation Q split c).Equiv
      (Representation.SuzukiNatural.natural m)) :
    ∃ a : Representation.SuzukiNatural.F m, a ≠ 0 ∧
      ∀ v : Additive (V2Section Q split c).Carrier,
        e₂.toLinearEquiv v = a • e₁.toLinearEquiv v := by
  exact natural_intertwiner_scalar_unique (suzukiV2Representation Q split c) e₁ e₂

include c in
/-- The same scalar uniqueness holds for the Φ(V)/Z(V) layer. -/
theorem phiCenterCoordinates_choice_scalar
    (e₁ e₂ : (suzukiPhiCenterRepresentation Q split c).Equiv
      (Representation.SuzukiNatural.natural m)) :
    ∃ a : Representation.SuzukiNatural.F m, a ≠ 0 ∧
      ∀ v : Additive (phiCenterSection Q split c).Carrier,
        e₂.toLinearEquiv v = a • e₁.toLinearEquiv v := by
  exact natural_intertwiner_scalar_unique (suzukiPhiCenterRepresentation Q split c) e₁ e₂

/-- In particular the canonical coordinate chosen in `NaturalLayers` has the
same action formulas as every other choice, up to the displayed scalar. -/
theorem V2Coordinates_choice_scalar_apply
    (e : (suzukiV2Representation Q split c).Equiv
      (Representation.SuzukiNatural.natural m)) :
    ∃ a : Representation.SuzukiNatural.F m, a ≠ 0 ∧
      ∀ v : Additive (V2Section Q split c).Carrier,
        e.toLinearEquiv v = a • V2Coordinates Q split c v := by
  exact V2Coordinates_choice_scalar Q split c
    (V2Coordinates Q split c) e

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
