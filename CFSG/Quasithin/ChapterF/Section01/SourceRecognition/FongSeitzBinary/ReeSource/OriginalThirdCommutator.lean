module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.ThirdCommutator
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalDerivedProduct

/-!
# The third commutator and mixed identities on the original quotient

The actual endpoint map transports the third commutator of the original
two-core to the perpendicular Omega root. The original Hypothesis F.1.1
also discharges the inputs to the remaining mixed identities (6H)(d,e).
The SourceQuotient applications keep the literal Q.q and endpoint inclusion.
Source: Fong--Seitz I (1973), (6H)(d,e,g), printed pp.55--56.
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
/-- The original two-core's third commutator maps onto the perpendicular Omega root. -/
theorem original_source_radical_third_image
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (⁅(⊤ : Subgroup (pCore 2 (parabolic L S 1))),frattini (pCore 2 (parabolic L S 1))⁆).map
      ((endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype) =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  let hV := marked_suzuki_remainder_le_kernel Q split 1 m μ hB
  let a := originalRadicalEquiv Q e split 1 hV
  have he : (endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype =
      (simpleRemainder Q split 1).subtype.comp a.toMonoidHom := by
    ext x
    exact (originalRadicalEquiv_apply Q e split 1 hV x).symm
  rw [map_commutator,original_source_radical_frattini_image Q e split n hn m ν T hC μ hB h hm,he,
    ←map_map,Subgroup.map_top_of_surjective a.toMonoidHom a.surjective,
    ←MonoidHom.range_eq_map,range_subtype]
  exact source_radical_third_eq_omega Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1)

include e ν hC μ hB hn in
/-- Both remaining mixed-root identities on the original marked quotient. -/
theorem original_source_remaining_mixed_identities
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    ⁅simpleRoot Q split 0,rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ = ⊥ ∧
      ⁅omegaOneAmbient (simpleRoot Q split 1),rootAt Q split 0 (Q.simple 1*Q.simple 0)⁆ =
        omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) :=
  ⟨source_linear_perpendicular_commute Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1),
   source_omega_far_linear_eq Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1)⟩

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
/-- The third commutator image with literally Q.q and the original endpoint inclusion. -/
theorem original_source_radical_third_image_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (⁅(⊤ : Subgroup (pCore 2 (parabolic L S 1))),frattini (pCore 2 (parabolic L S 1))⁆).map
      ((Q.q.comp (inclusion (parabolic_le_generated 1))).comp
        (pCore 2 (parabolic L S 1)).subtype) =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated 1)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 := by
    ext g
    exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_radical_third_image Q (originalMarkedIso Q) split n hn m ν T hC μ hB h hm

include ν hC μ hB hn in
/-- Both remaining mixed identities on the same original SourceQuotient. -/
theorem original_source_remaining_mixed_identities_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    ⁅simpleRoot Q split 0,rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ = ⊥ ∧
      ⁅omegaOneAmbient (simpleRoot Q split 1),rootAt Q split 0 (Q.simple 1*Q.simple 0)⁆ =
        omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) :=
  original_source_remaining_mixed_identities Q (originalMarkedIso Q) split n hn m ν T hC μ hB h hm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
