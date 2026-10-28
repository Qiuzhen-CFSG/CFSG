module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.FiveFactors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalDerivedFrattini

/-!
# Five-factor structure in the original two-core image

The elementary abelian subgroup of order q⁵ and the hypothetical whole
perpendicular-root alternative are applied to the actual original
Frattini image. Hypothesis F.1.1 discharges the Borel-core and two-core
centralizer premises. The SourceQuotient specializations use literally
Q.q composed with the original endpoint inclusion; the ambient group
need not be finite. The whole-root alternative is not excluded here.
Source: Fong--Seitz I (1973), proof of (6H)(f), printed p.55.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))


include ν hC μ hB hn in
/-- The actual original Frattini image contains the elementary five-factor subgroup of order q⁵. -/
theorem original_source_five_derived_data
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    IsElementaryAbelian 2 (fiveDerivedSubgroup Q split) ∧
      Nat.card (fiveDerivedSubgroup Q split) = (2^(2*m+1))^5 ∧
      fiveDerivedSubgroup Q split ≤ (frattini (pCore 2 (parabolic L S 1))).map
        ((endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype) := by
  have hcore := LinearThreePresentation.borel_core_eq_bot Q e h
  have hc := parabolic_core_selfCentralizing Q e h 1
  refine ⟨(source_five_derived_elementary_product Q split n hn m ν T hC μ hB hm hcore hc).1,
    source_five_derived_card Q split n hn m ν T hC μ hB hm hcore hc,?_⟩
  rw [original_source_radical_frattini_image Q e split n hn m ν T hC μ hB h hm]
  exact source_five_derived_le Q split n hn m ν T hC μ hB hm hcore hc

include ν hC μ hB hn in
/-- The p.55 whole-root reductio alternative in the same original Frattini image. -/
theorem original_source_perpendicular_in_derived_case
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8)
    (hE : rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) ≤
      (frattini (pCore 2 (parabolic L S 1))).map
        ((endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype)) :
    (frattini (pCore 2 (parabolic L S 1))).map
        ((endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype) =
      fiveDerivedSubgroup Q split ⊔ rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) ∧
    omegaOneAmbient ((frattini (pCore 2 (parabolic L S 1))).map
        ((endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype)) =
      fiveDerivedSubgroup Q split := by
  rw [original_source_radical_frattini_image Q e split n hn m ν T hC μ hB h hm] at hE ⊢
  exact source_perpendicular_in_derived_case Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1) hE

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))


include ν hC μ hB hn in
/-- The five-factor subgroup in the literal Q.q image of the original two-core Frattini subgroup. -/
theorem original_source_five_derived_data_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    IsElementaryAbelian 2 (fiveDerivedSubgroup Q split) ∧
      Nat.card (fiveDerivedSubgroup Q split) = (2^(2*m+1))^5 ∧
      fiveDerivedSubgroup Q split ≤ (frattini (pCore 2 (parabolic L S 1))).map
        ((Q.q.comp (inclusion (parabolic_le_generated 1))).comp
          (pCore 2 (parabolic L S 1)).subtype) := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated 1)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 := by
    ext g
    exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_five_derived_data Q (originalMarkedIso Q) split n hn m ν T hC μ hB h hm

include ν hC μ hB hn in
/-- The full perpendicular-root alternative, retaining the literal quotient and original inclusion. -/
theorem original_source_perpendicular_in_derived_case_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8)
    (hE : rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) ≤
      (frattini (pCore 2 (parabolic L S 1))).map
        ((Q.q.comp (inclusion (parabolic_le_generated 1))).comp
          (pCore 2 (parabolic L S 1)).subtype)) :
    (frattini (pCore 2 (parabolic L S 1))).map
        ((Q.q.comp (inclusion (parabolic_le_generated 1))).comp
          (pCore 2 (parabolic L S 1)).subtype) =
      fiveDerivedSubgroup Q split ⊔ rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) ∧
    omegaOneAmbient ((frattini (pCore 2 (parabolic L S 1))).map
        ((Q.q.comp (inclusion (parabolic_le_generated 1))).comp
          (pCore 2 (parabolic L S 1)).subtype)) =
      fiveDerivedSubgroup Q split := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated 1)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 := by
    ext g
    exact (originalMarkedIso_right_apply Q g).symm
  rw [hf] at hE ⊢
  exact original_source_perpendicular_in_derived_case Q (originalMarkedIso Q) split n hn m ν T hC μ hB h hm hE

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
