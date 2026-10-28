module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Centers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalThirdCommutator

/-!
# Full center identities on the original marked quotient

The actual endpoint and full-overlap maps carry the original two-core
center and Sylow center onto the same perpendicular Omega subgroup.
Hypothesis F.1.1 supplies the faithful Borel and local characteristic-two
premises. The SourceQuotient applications retain literally Q.q.
Source: Fong--Seitz I (1973), (6H)(g), p.55.
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
/-- The original two-core center has exactly the perpendicular Omega image. -/
theorem original_source_radical_center_image
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (center (pCore 2 (parabolic L S 1))).map
      ((endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype) =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  let hV := marked_suzuki_remainder_le_kernel Q split 1 m μ hB
  let a := originalRadicalEquiv Q e split 1 hV
  have he : (endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype =
      (simpleRemainder Q split 1).subtype.comp a.toMonoidHom := by
    ext x
    exact (originalRadicalEquiv_apply Q e split 1 hV x).symm
  rw [he,←map_map,center_map_equiv]
  exact source_radical_center_eq_omega Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1)

include ν hC μ hB hn in
/-- The original Sylow center follows the same full-overlap marking. -/
theorem original_source_sylow_center_image
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (center S).map (sylowMap Q e h) =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  have hf : Function.Injective (sylowMap Q e h) := Q.tits.B.subtype_injective.comp
    (((MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm).trans e.middle).injective.comp
      (inclusion_injective _))
  let a : S ≃* split.U := (MonoidHom.ofInjective hf).trans
    (MulEquiv.subgroupCongr (sylow_range Q e h split))
  have he : sylowMap Q e h = split.U.subtype.comp a.toMonoidHom := rfl
  rw [he,←map_map,center_map_equiv]
  exact source_unipotent_center_eq_omega Q split n hn m ν T hC μ hB hm
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
/-- The exact original two-core center image under literally Q.q. -/
theorem original_source_radical_center_image_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (center (pCore 2 (parabolic L S 1))).map
      ((Q.q.comp (inclusion (parabolic_le_generated 1))).comp
        (pCore 2 (parabolic L S 1)).subtype) =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated 1)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 := by
    ext g
    exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_radical_center_image Q (originalMarkedIso Q) split n hn m ν T hC μ hB h hm

include ν hC μ hB hn in
/-- The original Sylow center image uses the literal quotient on the same S. -/
theorem original_source_sylow_center_image_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (center S).map (Q.q.comp (inclusion
      ((show S ≤ parabolic L S 1 from le_sup_right.trans le_sup_left).trans
        (parabolic_le_generated 1)))) =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  have hf : Q.q.comp (inclusion
      ((show S ≤ parabolic L S 1 from le_sup_right.trans le_sup_left).trans
        (parabolic_le_generated 1))) = MarkedLocal.sylowMap Q (originalMarkedIso Q) h := by
    ext s
    exact (originalMarkedIso_right_apply Q
      ⟨s,(show S ≤ parabolic L S 1 from le_sup_right.trans le_sup_left) s.property⟩).symm.trans
      (MarkedLocal.endpoint_sylow Q (originalMarkedIso Q) h 1 s)
  rw [hf]
  exact original_source_sylow_center_image Q (originalMarkedIso Q) split n hn m ν T hC μ hB h hm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
