module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PositiveSixFourEquality
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.LinearNear
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalSeparatedNear
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearThreePresentation

/-!
# Original near and perpendicular commutator clauses for every parameter

The proved Suzuki perpendicular relation is pulled back along the injective
original endpoint map. The original hypotheses discharge self-centralization
of the two-core and faithfulness of the quotient Borel. The specialization
uses literally Q.q composed with the original parabolic inclusion; the
ambient group need not be finite. All three relations include q=2, and the (6.4) equality retains the actual
root Omega. Source: Fong--Seitz I (6H)(d), p.54.
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
/-- Perpendicular commutation for every parameter in the literal original endpoint. -/
theorem original_source_perpendicular_commute
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    ⁅(simpleRoot Q split 1).comap (endpointMap Q e 1),
      (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)).comap (endpointMap Q e 1)⁆ = ⊥ := by
  apply map_injective (f := endpointMap Q e 1)
    ((Endpoint Q 1).subtype_injective.comp (endpoint Q e 1).injective)
  rw [map_commutator,Subgroup.map_bot]
  apply eq_bot_iff.mpr
  exact (commutator_mono (map_comap_le _ _) (map_comap_le _ _)).trans
    (source_perpendicular_commute Q split n hn m ν T hC μ hB hm
      (LinearThreePresentation.borel_core_eq_bot Q e h)
      (parabolic_core_selfCentralizing Q e h 1)).le


include ν hC μ hB hn in
/-- Linear near-root commutation on the same original endpoint, including q=2. -/
theorem original_source_linear_near_commute
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    ⁅(simpleRoot Q split 0).comap (endpointMap Q e 1),
      (rootAt Q split 0 (Q.simple 1*Q.simple 0)).comap (endpointMap Q e 1)⁆ = ⊥ := by
  apply map_injective (f := endpointMap Q e 1)
    ((Endpoint Q 1).subtype_injective.comp (endpoint Q e 1).injective)
  rw [map_commutator,Subgroup.map_bot]
  apply eq_bot_iff.mpr
  exact (commutator_mono (map_comap_le _ _) (map_comap_le _ _)).trans
    (source_linear_near_commute Q split n hn m ν T hC μ hB hm
      (LinearThreePresentation.borel_core_eq_bot Q e h)
      (parabolic_core_selfCentralizing Q e h 1)).le

private theorem endpoint_image (A : Subgroup (X ⧸ Q.D)) (hA : A ≤ Endpoint Q 1) :
    (A.comap (endpointMap Q e 1)).map (endpointMap Q e 1) = A := by
  have hr : (endpointMap Q e 1).range = Endpoint Q 1 := by
    rw [endpointMap,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (endpoint Q e 1).surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  rw [map_comap_eq,hr]
  exact inf_eq_right.mpr hA

include ν hC μ hB hn in
/-- The full (6.4) equality for every parameter on the original endpoint, with its actual Omega. -/
theorem original_source_six_four_eq
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    ⁅(simpleRoot Q split 1).comap (endpointMap Q e 1),
      (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)).comap (endpointMap Q e 1)⁆ =
      omegaOneAmbient ((rootAt Q split 1 (Q.simple 0*Q.simple 1)).comap (endpointMap Q e 1)) := by
  have hUP : split.U ≤ Endpoint Q 1 := split.U_le.trans (Q.tits.B_le_standardParabolic _)
  have hD : rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) ≤ Endpoint Q 1 := by
    apply le_trans ?_ hUP
    rw [←unipotentConjugate_one split]
    apply rootAt_le_conjugate
    have hs (k : Fin 2) : (Q.simple k)⁻¹ = Q.simple k := inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2)
    simp only [one_mul,mul_inv_rev,hs,←mul_assoc]
    have h3 := wordLength_alternatingWord Q true (n := 3) (by omega)
    have h4 := wordLength_alternatingWord Q true (n := 4) (by omega)
    simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,mul_one,←mul_assoc] at h3 h4
    rw [h3,h4]
  have hi := (Endpoint Q 1).subtype_injective.comp (endpoint Q e 1).injective
  apply map_injective (f := endpointMap Q e 1) hi
  rw [map_commutator,endpoint_image Q e _ ((simpleRoot_le Q split 1).trans hUP),
    endpoint_image Q e _ hD,map_omegaOneAmbient_injective _ hi,
    endpoint_image Q e _ ((octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).2.1.trans
      (inf_le_left.trans hUP))]
  exact source_six_four_eq Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1)

set_option linter.unusedVariables false in
include ν hC μ hB hn in
/-- Existing positive-parameter specialization, retained for compatibility. -/
theorem original_source_positive_perpendicular_commute
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hmpos : 0 < m) :
    ⁅(simpleRoot Q split 1).comap (endpointMap Q e 1),
      (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)).comap (endpointMap Q e 1)⁆ = ⊥ := by
  exact original_source_perpendicular_commute Q e split n hn m ν T hC μ hB h hm

set_option linter.unusedVariables false in
include ν hC μ hB hn in
/-- Existing positive-parameter specialization, retained for compatibility. -/
theorem original_source_positive_six_four_eq
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hmpos : 0 < m) :
    ⁅(simpleRoot Q split 1).comap (endpointMap Q e 1),
      (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)).comap (endpointMap Q e 1)⁆ =
      omegaOneAmbient ((rootAt Q split 1 (Q.simple 0*Q.simple 1)).comap (endpointMap Q e 1)) := by
  exact original_source_six_four_eq Q e split n hn m ν T hC μ hB h hm

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
/-- The same source clause for Q.q and the original endpoint inclusion. -/
theorem original_source_perpendicular_commute_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    ⁅(simpleRoot Q split 1).comap (Q.q.comp (inclusion (parabolic_le_generated 1))),
      (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)).comap
        (Q.q.comp (inclusion (parabolic_le_generated 1)))⁆ = ⊥ := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated 1)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 := by
    ext g
    exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_perpendicular_commute Q (originalMarkedIso Q) split n hn m ν T hC μ hB h hm

include ν hC μ hB hn in
/-- The linear near relation with the literal original quotient map. -/
theorem original_source_linear_near_commute_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    ⁅(simpleRoot Q split 0).comap (Q.q.comp (inclusion (parabolic_le_generated 1))),
      (rootAt Q split 0 (Q.simple 1*Q.simple 0)).comap
        (Q.q.comp (inclusion (parabolic_le_generated 1)))⁆ = ⊥ := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated 1)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 := by
    ext g
    exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_linear_near_commute Q (originalMarkedIso Q) split n hn m ν T hC μ hB h hm

include ν hC μ hB hn in
/-- All-parameter (6.4) on the literal original quotient, with no nonzero premise. -/
theorem original_source_six_four_eq_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    ⁅(simpleRoot Q split 1).comap (Q.q.comp (inclusion (parabolic_le_generated 1))),
      (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)).comap
        (Q.q.comp (inclusion (parabolic_le_generated 1)))⁆ =
      omegaOneAmbient ((rootAt Q split 1 (Q.simple 0*Q.simple 1)).comap
        (Q.q.comp (inclusion (parabolic_le_generated 1)))) := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated 1)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 := by
    ext g
    exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_six_four_eq Q (originalMarkedIso Q) split n hn m ν T hC μ hB h hm

set_option linter.unusedVariables false in
include ν hC μ hB hn in
/-- Existing positive-parameter specialization, retained for compatibility. -/
theorem original_source_positive_perpendicular_commute_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hmpos : 0 < m) :
    ⁅(simpleRoot Q split 1).comap (Q.q.comp (inclusion (parabolic_le_generated 1))),
      (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)).comap
        (Q.q.comp (inclusion (parabolic_le_generated 1)))⁆ = ⊥ := by
  exact original_source_perpendicular_commute_quotient Q split n hn m ν T hC μ hB h hm

set_option linter.unusedVariables false in
include ν hC μ hB hn in
/-- Existing positive-parameter specialization, retained for compatibility. -/
theorem original_source_positive_six_four_eq_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hmpos : 0 < m) :
    ⁅(simpleRoot Q split 1).comap (Q.q.comp (inclusion (parabolic_le_generated 1))),
      (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)).comap
        (Q.q.comp (inclusion (parabolic_le_generated 1)))⁆ =
      omegaOneAmbient ((rootAt Q split 1 (Q.simple 0*Q.simple 1)).comap
        (Q.q.comp (inclusion (parabolic_le_generated 1)))) := by
  exact original_source_six_four_eq_quotient Q split n hn m ν T hC μ hB h hm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
