module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PerpendicularExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalDerivedFrattini

/-!
# The derived-radical involution argument on the original quotient

The p.55 involution argument excludes whole-perpendicular-root containment
in the actual original Frattini image and identifies its perpendicular
intersection as Omega. Its intermediate far-linear commutator bound is
retained as well.
The characteristic-two and faithful-Borel premises follow from the original
Hypothesis F.1.1; the second specialization retains literally Q.q and the
endpoint inclusion. The remaining source identities and recognition are
not asserted by these applications.
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
/-- The p.55 far-linear commutator calculation on the original two-core Frattini image. -/
theorem original_source_far_linear_le_five_of_perpendicular_le
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8)
    (hE : rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) ≤
      (frattini (pCore 2 (parabolic L S 1))).map
        ((endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype)) :
    ⁅simpleRoot Q split 0,rootAt Q split 0 (Q.simple 1)⁆ ≤ fiveDerivedSubgroup Q split := by
  rw [original_source_radical_frattini_image Q e split n hn m ν T hC μ hB h hm] at hE
  exact source_far_linear_le_five_of_perpendicular_le_derived Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1) hE

include ν hC μ hB hn in
/-- The whole perpendicular root is excluded from the actual original Frattini image. -/
theorem original_source_perpendicular_not_le_frattini
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    ¬ rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) ≤
      (frattini (pCore 2 (parabolic L S 1))).map
        ((endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype) := by
  rw [original_source_radical_frattini_image Q e split n hn m ν T hC μ hB h hm]
  exact source_perpendicular_not_le_derived Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1)

include ν hC μ hB hn in
/-- The perpendicular intersection of the original Frattini image is exactly Omega. -/
theorem original_source_frattini_inf_perpendicular
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (frattini (pCore 2 (parabolic L S 1))).map
        ((endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype) ⊓
      rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  rw [original_source_radical_frattini_image Q e split n hn m ν T hC μ hB h hm]
  exact source_derived_inf_perpendicular_eq_omega Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1)

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
/-- The same reductio calculation uses literally Q.q and the original endpoint inclusion. -/
theorem original_source_far_linear_le_five_of_perpendicular_le_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8)
    (hE : rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) ≤
      (frattini (pCore 2 (parabolic L S 1))).map
        ((Q.q.comp (inclusion (parabolic_le_generated 1))).comp
          (pCore 2 (parabolic L S 1)).subtype)) :
    ⁅simpleRoot Q split 0,rootAt Q split 0 (Q.simple 1)⁆ ≤ fiveDerivedSubgroup Q split := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated 1)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 := by
    ext g
    exact (originalMarkedIso_right_apply Q g).symm
  rw [hf] at hE
  exact original_source_far_linear_le_five_of_perpendicular_le Q (originalMarkedIso Q)
    split n hn m ν T hC μ hB h hm hE

include ν hC μ hB hn in
/-- Whole-root exclusion with the literal quotient map and original endpoint inclusion. -/
theorem original_source_perpendicular_not_le_frattini_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    ¬ rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) ≤
      (frattini (pCore 2 (parabolic L S 1))).map
        ((Q.q.comp (inclusion (parabolic_le_generated 1))).comp
          (pCore 2 (parabolic L S 1)).subtype) := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated 1)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 := by
    ext g
    exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_perpendicular_not_le_frattini Q (originalMarkedIso Q)
    split n hn m ν T hC μ hB h hm

include ν hC μ hB hn in
/-- The exact perpendicular intersection in the literal Q.q image of the original Frattini subgroup. -/
theorem original_source_frattini_inf_perpendicular_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (frattini (pCore 2 (parabolic L S 1))).map
        ((Q.q.comp (inclusion (parabolic_le_generated 1))).comp
          (pCore 2 (parabolic L S 1)).subtype) ⊓
      rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated 1)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 := by
    ext g
    exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_frattini_inf_perpendicular Q (originalMarkedIso Q)
    split n hn m ν T hC μ hB h hm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
