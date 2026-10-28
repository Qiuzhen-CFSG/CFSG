module
public import Theory.Representation.SU3.ProjectiveBinaryDegree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryScalarDerived

/-!
# The eight-b bound on the original scalar-fixed derived section

The original linear and SU₃/PSU₃ factors give an odd unitary degree and the
same scalar-fixed derived effective section. Its already constructed faithful
projective representation has binary dimension at least 8b when b ≥ 2.
At b = 1 the established order-256 bound supplies the same conclusion.
The original section, its containment of the cubic radical centralizer,
the actor identification and the literal projection equation are retained.
Both endpoint orientations and both special/projective conventions are covered.

Source: Fong--Seitz I (4D), printed pp.21--23, applied in (6F), printed p.47.
This is the section-size step; invariant-subgroup exclusion and the subsequent
lower-central contradiction are separate arguments.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
include e h split

/-- The original scalar-fixed derived effective carrier has order at least
`2^(8*b)`, with the same faithful action and projection square, for all b > 0. -/
theorem original_linear_unitary_projective_degree
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x,J.conj x=x^(2^b))
    (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
    ∃ (hKj : simpleRemainder Q split j ≤ localKernel Q j)
      (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J),
      let d := unitaryScalarDerivedSection Q split j hKj
      rankOneScalar Q split j ≤ cartanThreeCore Q ∧
      simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤ d.numerator ∧
      d.action ≠ 1 ∧ d.effectiveAction.ker=(RootLocalCover.projection Q split j).ker ∧
      ∃ ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J)
          (Additive d.EffectiveCarrier),
        Function.Injective ρ ∧
        (∀ r, ρ (μ (RootLocalCover.projection Q split j r))=d.effectiveRepresentation r) ∧
        2^(8*b) ≤ Nat.card d.EffectiveCarrier := by
  obtain ⟨hKj,μ,hZ,hY,hmoving,hker,ρ,hfaith,hsquare,_,hsmall⟩ :=
    original_linear_unitary_scalar_derived_projective Q e h split hm i j hij ha hb hi J
      hcard hconj hmodel
  refine ⟨hKj,μ,hZ,hY,hmoving,hker,ρ,hfaith,hsquare,?_⟩
  by_cases hb1 : b=1
  · simpa only [hb1,mul_one,Nat.reducePow] using hsmall hb1
  · have hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
        IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) := by
      rcases hmodel with hp | hs
      · exact Or.inl ⟨F,inferInstance,inferInstance,J,hcard,hconj,hp⟩
      · exact Or.inr ⟨F,inferInstance,inferInstance,J,hcard,hconj,hs⟩
    have hodd := (original_linear_unitary_all_quadratic_degree
      Q e h split hm i j hij ha hb hi hj).1
    have hd := Representation.SU3.ProjectiveBinaryDegree.finrank_ge
      J (by omega) hodd hcard hconj ρ hfaith
    let d := unitaryScalarDerivedSection Q split j hKj
    have hc : Nat.card d.EffectiveCarrier =
        2 ^ Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) := by
      change Nat.card (Additive d.EffectiveCarrier) = _
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive d.EffectiveCarrier))
    rw [hc]
    exact Nat.pow_le_pow_right (by decide) hd

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
