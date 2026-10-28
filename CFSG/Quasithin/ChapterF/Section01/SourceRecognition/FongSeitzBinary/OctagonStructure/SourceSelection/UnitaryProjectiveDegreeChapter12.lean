module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryProjectiveDegree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.UnitaryDerivedChapter12

/-!
# Chapter 12's actual eight-b projective derived-section bound

The original SU₃/PSU₃ alternative constructs the same Hermitian model,
scalar-fixed derived section and faithful projective action as before, now
with order at least 2^(8b) for every positive b. The degree-one case uses
the established order-256 bound, while higher odd degrees use the proved
unitary tensor and Frobenius-period theorem. No representation premise is added.
The full Borel, original quotient and literal local projection square remain.

Source: Fong--Seitz I (4D), pp.21--23, and (6F), p.47, at AS 12.2.2.
This proves the section-size step, not the later commutator contradiction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.OctagonStructure
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits) (hm : rotationOrder Q = 8)
include D h hmany hn d hTH e split hm

/-- The literal Chapter 12 unitary alternative has a scalar-fixed derived
effective section of order at least `2^(8*b)`, including b = 1. -/
theorem rankOne_octagon_unitary_projective_degree
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (J : HermitianForm 3 F),
      Nat.card F=(2^b)^2 ∧ (∀ x,J.conj x=x^(2^b)) ∧
      ∃ (hK : simpleRemainder Q split 1 ≤ localKernel Q 1)
        (μ : localGroup Q split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J),
        let c := unitaryScalarDerivedSection Q split 1 hK
        rankOneScalar Q split 1 ≤ cartanThreeCore Q ∧
        simpleRemainder Q split 1 ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤ c.numerator ∧
        c.action ≠ 1 ∧ c.effectiveAction.ker=(RootLocalCover.projection Q split 1).ker ∧
        ∃ ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J)
            (Additive c.EffectiveCarrier),
          Function.Injective ρ ∧
          (∀ r, ρ (μ (RootLocalCover.projection Q split 1 r))=c.effectiveRepresentation r) ∧
          2^(8*b) ≤ Nat.card c.EffectiveCarrier := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  rcases hR with ⟨F,hF,hfin,J,hcard,hconj,hmodel⟩ | ⟨F,hF,hfin,J,hcard,hconj,hmodel⟩
  · refine ⟨F,hF,hfin,J,hcard,hconj,?_⟩
    exact original_linear_unitary_projective_degree Q e hf split hm 0 1 (by decide)
      (by omega) hb hpsl J hcard hconj (Or.inl hmodel)
  · refine ⟨F,hF,hfin,J,hcard,hconj,?_⟩
    exact original_linear_unitary_projective_degree Q e hf split hm 0 1 (by decide)
      (by omega) hb hpsl J hcard hconj (Or.inr hmodel)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
