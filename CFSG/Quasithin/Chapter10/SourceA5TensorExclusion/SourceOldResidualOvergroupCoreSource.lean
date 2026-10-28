module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualOvergroupCoreSetup
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualOvergroupCoreBorels
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanTwoCore.Tensor

/-!
# Original tensor input for the nonzero overgroup-core argument

The 9.3.2 Cartan core equality and the original cubic Borels discharge
all local preparation in the F.1.1 entrance. Under O₂(M₀)=1 the literal
pair (L,K) therefore satisfies genuine F.1.1, has both A₅ quotients,
is quasithin, and has both Borels normalizing the original common S.

The remaining independent F.1.12 A₅-pair containment theorem would give
S≤L, contradicting the explicit opposite-factor Sylow witness. The last
two theorems retain precisely that recognition premise and apply the
resulting nonzero core to the existing original field-four consumer.
They are conditional source assembly, not a proof of F.1.12 or a claim
that the nonzero-core source is complete.

Source: Aschbacher--Smith 9.3.3, printed p.733, and F.1.12(I)--(II),
printed pp.262--264. The source Cartan normalization is 9.3.1.
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

/-- All rank-two input on the original pair, with 9.3.2 and Borel enclosure discharged. -/
theorem old_residual_core_zero_rank_two_source
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
    ChapterF.Source.HypothesisF11 ![L,(pResidual 2 H).map H.subtype] (commonTwo T L) ∧
    IsQuasithin (ChapterF.Source.generated ![L,(pResidual 2 H).map H.subtype] (commonTwo T L)) ∧
    (∀ i : Fin 2, Nonempty ((![L,(pResidual 2 H).map H.subtype] i ⧸
      pCore 2 (![L,(pResidual 2 H).map H.subtype] i)) ≃* alternatingGroup (Fin 5))) ∧
    (∀ i : Fin 2, ChapterF.Source.borel
      (![L,(pResidual 2 H).map H.subtype] i) (commonTwo T L) ≤
        normalizer (commonTwo T L : Set G)) := by
  have hS := m.source_cartan_twoCore_eq_old_residual hH eK A B hAB hA9 hBA hBK hB3 hAK
  have hST := m.old_residual_commonTwo_le_stabilizer.trans inf_le_left
  have hAS : A ≤ normalizer (commonTwo T L : Set G) :=
    hAB.trans (old_residual_commonTwo_borel_normalized (T := T) (L := L))
  have hB : ∀ i : Fin 2, ChapterF.Source.borel
      (![L,(pResidual 2 H).map H.subtype] i) (commonTwo T L) ≤ A ⊔ commonTwo T L := by
    intro i
    fin_cases i
    · exact m.old_residual_component_borel_le_cartan_sup A _ hAB hA9 hST le_sup_left hAS
    · exact old_residual_borel_le_cartan_sup hH eK A B _ hBA hBK hB3 hST
        (le_sup_left.trans_eq hS.symm) hAS
  exact m.old_residual_core_zero_rank_two_data hH eK A hAB hAK hS hB M₀ hgen hzero

/-- The terminal 9.3.3 implication with the independent F.1.12 recognition premise explicit. -/
theorem old_residual_overgroup_core_ne_bot_of_rank_two_containment
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
    (hcontain : ∀ (P : Fin 2 → Subgroup G) (S : Subgroup G),
      ChapterF.Source.HypothesisF11 P S → IsQuasithin (ChapterF.Source.generated P S) →
      (∀ i, Nonempty ((P i ⧸ pCore 2 (P i)) ≃* alternatingGroup (Fin 5))) →
      (∃ j, ChapterF.Source.borel (P j) S ≤ normalizer (S : Set G)) → ∀ i, S ≤ P i)
    : pCore 2 M₀ ≠ ⊥ := by
  intro hzero
  obtain ⟨hf,hqt,hq,hn⟩ := m.old_residual_core_zero_rank_two_source
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hzero
  exact m.old_residual_common_sylow_not_le_component
    (hcontain _ _ hf hqt hq ⟨0,hn 0⟩ 0)

/-- Actual original field-four consumer, using the core obtained from F.1.12. -/
theorem old_residual_overgroup_fourField_models_of_rank_two_containment
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
    (hcontain : ∀ (P : Fin 2 → Subgroup G) (S : Subgroup G),
      ChapterF.Source.HypothesisF11 P S → IsQuasithin (ChapterF.Source.generated P S) →
      (∀ i, Nonempty ((P i ⧸ pCore 2 (P i)) ≃* alternatingGroup (Fin 5))) →
      (∃ j, ChapterF.Source.borel (P j) S ≤ normalizer (S : Set G)) → ∀ i, S ≤ P i)
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
  have hcore := m.old_residual_overgroup_core_ne_bot_of_rank_two_containment
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hcontain
  exact m.old_residual_overgroup_fourField_models_of_no_linear_three_four
    hH hlarge hlinear houtside M₀ hcore hgen hKU

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
