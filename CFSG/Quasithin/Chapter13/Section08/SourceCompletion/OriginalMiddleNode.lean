module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalOrdinaryTransvections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource.Source

/-!
# The actual middle node is excluded at the original ordinary source

The literal S₈ actor has order greater than 720, so ordinary source
transvection recognition excludes rank-one displacement. The original flag
then constructs the strict quadratic pair and its rank-two seed. The marked
middle-node quotient and the proved B.4 classifications exclude this case.
All component structure, earlier component clauses and whole-action inputs
come from the unchanged original source. No universal local-input family
or middle-node, orthogonal quotient or B.4 callback is assumed.
Source: Aschbacher--Smith 13.8.25, printed pp.959--960.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open ComponentSieve.AlternatingAndLinear
open LinearReduction
open FourStructure.ChiefFactors FourStructure.ChiefFactors.Alignment
open OrthogonalQuotient.B4Extraction
open ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules
open Chapter2.ComponentRefinement.LieType.Binary
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
open ComponentSieve

private theorem middleNode_coordinates {G : Type*} [Group G] [Finite G] (H K L₁ T : Subgroup G)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* PSL 4)
    (hm : Parabolics.MiddleNodeMarking H K L₁ T hKH hK e) :
    ∃ (eH : Source.Hstar H ≃* Equiv.Perm (Fin 8))
      (eK : Source.starImage H K ≃* BinaryLinear.GL OrthogonalQuotient.FourSpace)
      (A F : Submodule (ZMod 2) OrthogonalQuotient.FourSpace),
      (Source.starImage H K).map eH.toMonoidHom = alternatingGroup (Fin 8) ∧
      A ≤ F ∧ Module.finrank (ZMod 2) A = 1 ∧
      Module.finrank (ZMod 2) F + 1 = Module.finrank (ZMod 2) OrthogonalQuotient.FourSpace ∧
      ((Source.starImage H L₁ ⊔ (Source.starImage H K ⊓ Source.starImage H T)).subgroupOf
        (Source.starImage H K)).map eK.toMonoidHom = BinaryLinear.parabolic A ⊓ BinaryLinear.parabolic F := by
  obtain ⟨b, i, hi, hp, _, _, _, _, eH, _, heH, _⟩ := hm
  have hi' : i = 1 := Fin.ext (by simpa using hi)
  subst i
  let eK := linearModel (Parabolics.starLinearEquiv H K hKH hK e)
  refine ⟨eH, eK, cutSpace b 0, cutSpace b 2, heH,
    BinaryLinear.InvariantNodeActions.cutSpace_mono b (by decide), ?_, ?_, ?_⟩
  · exact BinaryLinear.InvariantNodeActions.cutSpace_finrank b 0
  · change Module.finrank (ZMod 2) (BinaryLinear.InvariantNodeActions.cutSpace b 2) + 1 = _
    rw [BinaryLinear.InvariantNodeActions.cutSpace_finrank]
    norm_num [OrthogonalQuotient.FourSpace, Module.finrank_pi]
  · have hp' := Parabolics.OuterAction.deletedFlag_linear_image (by decide : 2 ≤ 3)
      (Parabolics.starLinearEquiv H K hKH hK e) b 1
    rw [← hp] at hp'
    change _ = _ at hp'
    rw [inf_comm (Source.starImage H K)]
    change ((Parabolics.OrdinarySource.sourceNode H K L₁ T).subgroupOf (Source.starImage H K)).map
      (linearModel (Parabolics.starLinearEquiv H K hKH hK e)).toMonoidHom = _
    rw [hp']
    change BinaryLinear.InvariantNodeActions.minimalParabolic b 1 = _
    ext g
    simp only [BinaryLinear.InvariantNodeActions.minimalParabolic,
      BinaryLinear.InvariantNodeActions.cutStabilizer, mem_iInf, mem_inf]
    simp [Fin.forall_fin_succ]
    rfl


universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- Exclude the actual marked middle node using only the original ordinary
source geometry and the prescribed component. -/
theorem original_middle_node_exclusion_of_plane_noncentral
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (sourceOne L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* PSL 4) :
    ¬ Parabolics.MiddleNodeMarking H K (sourceOne L T V₁) T hKH hK e := by
  intro hmiddleNode
  have hF9 := hF9all H hH
  have hm' : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥ := by
    rwa [← d.first_normalizer]
  have hcentral := Section05.AmbientSource.source_parabolic_centralizer
    (localNaturalSetup d) eL hmax hm'
  have hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥ := by
    intro he
    apply hm
    apply bot_unique
    rw [commutator_comm] at he
    exact (commutator_mono le_rfl d.plane_le_seed).trans_eq he
  have earlier := original_earlier_inputs_of_ordinary_plane_noncentral d eL hmax hF9all hm
  have components := FieldComponents.LinearThree.OriginalExclusion.original_component_conclusions
    d hmax hF9all hcentral hcomm
  have groups := FieldComponents.LinearThree.OriginalExclusion.original_linear_group_facts
    d hmax hF9all hcentral hcomm
  have hN := groups.component_normal hH hKH hK
  have hLK := components.base_le hH hKH hK
  have hKT := (groups.supplement hH hKH hK).symm
  classical
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hH
  let : (V₁.subgroupOf (Source.UH H V₃)).Normal := inferInstance
  let a := Comparison.conjugationAction (d.line_le_uh H) hF9.plus_le_H
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) hF9.commutator_UH_QH_le_point
  let ρ := a.representation
  have hρ : IsSourceAction H V₃ V₁ ρ := a.conjugation
  obtain ⟨eH, eK, A, F, hKalt, hAF, hA, hF, hmiddle⟩ :=
    middleNode_coordinates H K (sourceOne L T V₁) T hKH hK e hmiddleNode
  have hcard : 720 < Nat.card (Source.Hstar H) := by
    rw [Nat.card_congr eH.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hno := original_no_rank_one_of_star_card_gt720 d eL hmax hF9all hm hH hcard ρ hρ
  let : IsQuasisimple (alternatingGroup (Fin 8)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hqs : IsQuasisimple (Source.starImage H K) :=
    IsQuasisimple.of_mulEquiv ((Parabolics.starLinearEquiv H K hKH hK e).trans
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).symm
  have hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)) := by
    rw [← hKT, ← sup_assoc, sup_eq_left.mpr hLK]
  obtain ⟨w⟩ := CriticalSource.exists_selected_witness d hH hF9 hgen hK hN hqs
    hcentral hcomm ρ hρ hno
  have hLh : sourceOne L T V₁ ≤ H := hLK.trans hKH
  have hTh : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have hP : Source.starImage H (sourceOne L T V₁ ⊔ (T : Subgroup G)) =
      Source.starImage H (sourceOne L T V₁) ⊔ Source.starImage H (T : Subgroup G) := by
    unfold Source.starImage
    rw [subgroupOf_sup hLh hTh, Subgroup.map_sup]
  have hline : V₁ < V₃ := by
    refine lt_of_le_of_ne (d.line_le_plane.trans d.plane_le_seed) ?_
    intro he
    have hc := d.line_card
    rw [he, d.seed_card] at hc
    omega
  let seed := sourceSeedOfEarlier H V₃ V₁ ρ hρ (sourceOne L T V₁ ⊔ (T : Subgroup G))
    T (sup_le hLh hTh) le_sup_right T.isPGroup' (Seven.OriginalSource.source_seed_normalized d)
    hline (fun X hZX hXV hPX => FourStructure.OriginalSource.seed_irreducible_source
      d hLh ρ hρ X hZX hXV (le_sup_left.trans hPX))
    (FourStructure.OriginalSource.seed_index_source d)
  have hstable : ∀ g : (Source.starImage H (sourceOne L T V₁) ⊔
      Source.starImage H (T : Subgroup G) : Subgroup (Source.Hstar H)),
      ∀ v ∈ sourceSeedSpace H V₃ V₁, ρ g v ∈ sourceSeedSpace H V₃ V₁ := by
    rw [← hP]
    exact seed.space.apply_mem_toSubmodule
  have hirr : IsAtom (⟨sourceSeedSpace H V₃ V₁, hstable⟩ : Subrepresentation
      (ρ.comp (Source.starImage H (sourceOne L T V₁) ⊔ Source.starImage H (T : Subgroup G)).subtype)) := by
    revert hstable
    rw [← hP]
    intro hstable
    exact seed.irreducible
  have hseedcomm : subspaceCommutator ρ (sourceSeedSpace H V₃ V₁)
      (Source.starImage H (sourceOne L T V₁)) = sourceSeedSpace H V₃ V₁ := by
    apply Components.Swapped.LinearTwo.ModuleAlternatives.image_commutator_eq H V₃ V₁ ρ hρ
      (sourceOne L T V₁) V₃ hLh (le_conjugateSpanBy V₃ H)
      (Section07.ModelExclusions.point_residual_normalizes_seed (localNaturalSetup d)) (d.line_le_uh H)
    rw [commutator_comm, Section07.ModelExclusions.seed_commutator_point_residual (localNaturalSetup d)]
    exact le_sup_left
  have hfull := Seven.OriginalSource.source_generated_original d hKH hN hLK
  obtain ⟨W, hw⟩ := OrthogonalQuotient.exists_source_quotient H V₃ V₁ L (sourceOne L T V₁)
    T G₁ M K (w.pair.Ugamma V₃) ρ hρ hH (d.line_le_uh H) hKH hK hLK hfull
    eH hKalt eK A F hAF hA hF hmiddle (T.isPGroup'.comap_subtype.map _)
    hstable hirr seed.dim_two hseedcomm
    w.quadratic_member.1 w.quadratic_member.2.1 w.quadratic_member.2.2
    (LinearReduction.OriginalSource.symmetric_b4 (Source.starImage H K) eH hKalt) (LinearReduction.OriginalSource.component_b4 (Source.starImage H K) eH eK hKalt) (Seven.OriginalSource.alternating_natural d earlier ρ)
  exact LinearReduction.OriginalSource.orthogonal_quotient_exclusion_source d hH hF9 hKH hN hLK ρ hρ w W hw.maximal
    eH hKalt hw.natural hw.component_moves (LinearReduction.OriginalSource.symmetric_b4 (Source.starImage H K) eH hKalt) (fun eK => LinearReduction.OriginalSource.component_b4 (Source.starImage H K) eH eK hKalt)

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
