module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualOvergroupCoreSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCoreRecognition

/-!
# The original overgroup core from source core control

The original tensor configuration supplies every F.1.1 hypothesis, both
A5 quotient markings, quasithinness and Borel normalization under O2(M0)=1.
The source core-control obligation then gives containment of the common
two-group in L, contradicting the original opposite-factor Sylow witness.
This supplies the nonzero core to the original field-four consumer without
requiring a semidirect complement to either local subgroup.

The first theorem also identifies an actual element of the canonical
quotient-action kernel outside L under O2(M0)=1. This is the obstruction
that a direct proof in the original tensor configuration must exclude.
The remaining theorems are conditional on `A5PairCoreRecognition`; they
do not establish that DGS85 recognition input.

Source: Aschbacher--Smith 9.3.3, printed p.733, and F.1.12, pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 SourceOldResidualOvergroup
open Chapter4 ChapterB ChapterE ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
open Representation Representation.BinaryOffender
open ChapterE.Section06.FixedPointBounds
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- Under a zero overgroup core, the original tensor configuration has
an actual quotient-action kernel element outside its original component. -/
theorem old_residual_core_zero_action_kernel_escape
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hBA : B ≤ A)
    (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (M₀ : Subgroup G)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hzero : pCore 2 M₀ = ⊥) :
    ∃ x : (L ⊔ commonTwo T L : Subgroup G),
      pCoreJoinAction 2 (m.old_residual_commonTwo_le_stabilizer.trans inf_le_right) x = 1 ∧
        (x : G) ∉ L := by
  obtain ⟨hf, _, _, hn⟩ := m.old_residual_core_zero_rank_two_source
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hzero
  exact hf.a5_local_action_kernel_escape_of_not_contained 0 e (hn 0)
    m.old_residual_common_sylow_not_le_component

/-- The terminal 9.3.3 implication from the source core-control obligation. -/
theorem old_residual_overgroup_core_ne_bot_of_core_recognition
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hBA : B ≤ A)
    (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (M₀ : Subgroup G)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (recognition : ChapterF.Source.A5PairCoreRecognition G)
    : pCore 2 M₀ ≠ ⊥ := by
  intro hzero
  obtain ⟨hf,hqt,hq,hn⟩ := m.old_residual_core_zero_rank_two_source
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hzero
  exact m.old_residual_common_sylow_not_le_component
    (ChapterF.Source.a5_pair_containment_of_core_recognition
      recognition hf hqt hq ⟨0,hn 0⟩ 0)

/-- The original field-four consumer, with source core recognition explicit. -/
theorem old_residual_overgroup_fourField_models_of_core_recognition
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hlinear : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      (pResidual 2 H).IsCComponent → IsQuasisimple (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) →
        ¬ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax (T.subtype hH.1.1.2) hP)
          (pResidual 2 H)) 3 4)
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (M₀ : Subgroup G)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (recognition : ChapterF.Source.A5PairCoreRecognition G)
    :
    m.tensorLine ≤ M₀.pCoreIn 2 ∧ M₀ ∈ Chapter1.He G ∧
      generalizedFitting M₀ = pCore 2 M₀ ∧ center M₀ = ⊥ ∧
    let R := ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      m.tensorLine.subgroupOf M₀ ≤ W ∧
      (pResidual 2 M₀).map (actionMk W) ≤ N ∧
      ChapterB.QuasisimpleSource.moved (ρ.comp N.subtype)
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) = ⊤ ∧
      ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) (((pResidual 2 M₀).map (actionMk W)).subgroupOf N),
      SourceA5TensorExclusion.FourWayFourField (ρ.comp N.subtype)
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) h.sectionData := by
  obtain ⟨eK⟩ := m.old_residual_a5_of_no_linear_three_four hH hlarge hlinear
  have hcore := m.old_residual_overgroup_core_ne_bot_of_core_recognition
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen recognition
  exact m.old_residual_overgroup_fourField_models_of_no_linear_three_four
    hH hlarge hlinear houtside M₀ hcore hgen hKU

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
