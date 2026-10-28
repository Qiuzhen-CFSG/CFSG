module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceProperSeven
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalRecognitionSource
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
import all CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalMovementAt

/-!
# Original H-star movement under the multiple-overgroup guard

The complete overcomponent reduction gives A₅, or an actual action of H
on seven letters through A₇ with solvable kernel. The first case gives the
known quotient-rank bound. In the second case minimal parabolicity puts
the solvable kernel in its normal core, whose intersection with T is O₂(H).
Every elementary subgroup of T disjoint from O₂(H) therefore embeds in A₇
and has order at most four. The original TI/weak-closure contradiction now
proves 12.2.18 in every branch, without a residual-marking or rank callback.

This is an internal continuation of `LocalConfigurationNaturalMovementAt`: its
private TI/rank-control lemmas are deliberately reused through `import all`,
without changing the existing public boundary.

The final adapter removes the rank premise from guarded natural recognition.
Solvability in 12.2.19 remains with qt-d-12213-hstar-natural; natural marking
and all movement premises in the solvable branch are discharged here.
Source: Aschbacher–Smith, 12.2.18–20, printed pp.800–802.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

/-- A nonsolvable minimal parabolic's solvable seven-letter kernel cannot
hide an elementary subgroup disjoint from its original two-core. -/
theorem chosen_hstar_small_disjoint_of_alternating_action_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H)
    (f : H →* alternatingGroup (Fin 7)) (hk : Group.IsSolvable f.ker)
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G))
    (hA : IsElementaryAbelian 2 A) (hd : Disjoint A (H.pCoreIn 2)) :
    Nat.card A ≤ 4 := by
  let := hk
  let := hA
  let S := T.subtype hH.1.1.2
  let hp := chosen_hstar_minimalParabolic_at h D structural hTI hH
  have hn : ¬ pResidual 2 H ≤ f.ker := by
    intro he
    let : Group.IsSolvable (pResidual 2 H) := Group.isSolvable_of_isSolvable_injective
      (f := inclusion he) (inclusion_injective he)
    let : Group.IsNilpotent (H ⧸ pResidual 2 H) := (isPGroup_quotient_pResidual 2).isNilpotent
    exact hs ((Group.isSolvable_iff_subgroup_quotient (pResidual 2 H)).mpr
      ⟨inferInstance,inferInstance⟩)
  have hkc : f.ker ≤ ChapterB.minimalParabolicCore S hp :=
    ChapterB.minimalParabolic_normal_le_core_of_residual_not_le S hp f.ker hn
  let i : A →* H := inclusion (hAT.trans hH.1.1.2)
  let g := f.comp i
  have hi : Function.Injective g := by
    apply g.ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    change x = 1
    apply Subtype.ext
    apply hd.le_bot
    refine ⟨x.property,?_⟩
    have hm : i x ∈ (S : Subgroup H) ⊓ ChapterB.minimalParabolicCore S hp :=
      ⟨hAT x.property,hkc hx⟩
    rw [ChapterB.minimalParabolic_sylow_inf_core S hp] at hm
    exact mem_map_of_mem H.subtype hm
  let j := (alternatingGroup (Fin 7)).subtype.comp g
  have hj : Function.Injective j := (alternatingGroup (Fin 7)).subtype_injective.comp hi
  let : IsElementaryAbelian 2 (⊤ : Subgroup A) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup A).subtype Subtype.val_injective
  let B := (⊤ : Subgroup A).map j
  have he : IsElementaryAbelian 2 B := IsElementaryAbelian.map j
  have hBA : B ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨a,_,rfl⟩
    exact (g a).property
  have hc := Representation.AlternatingSevenConjugatePair.ElementaryGeometry.elementary_even_card_le he hBA
  rw [card_map_of_injective hj,card_top] at hc
  exact hc

/-- Source 12.2.18 for every original H-star member, using only the actual
ambient structural and seven-module inputs and the standing guard. -/
theorem chosen_hstar_movement_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ V ≤ H.pCoreIn 2 := by
  by_cases hs : Group.IsSolvable H
  · exact chosen_movement_of_quotient_rank_at h D structural hnone hTI hH
      (chosen_hstar_quotient_rank_of_solvable_at h D structural hTI hH hs)
  obtain ⟨X,Y,C,_,hXY,hY⟩ := chosen_hstar_exists_residual_overcomponent_of_many_at
    h D structural modules hmany hnone hTI hH hs
  have hTX := C.normalized_of_overcomponent_at structural modules hH hXY hY
  by_cases he : X = Y
  · obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural Y hY).2.1
    have hf := (C.five_of_eq_at h D structural modules hTI hH hY he E).1
    exact chosen_movement_of_quotient_rank_at h D structural hnone hTI hH
      (chosen_hstar_quotient_rank_of_generating_five_component_at h D structural hTI hH C hTX (he.symm ▸ hf))
  rcases C.proper_five_or_alternating_action_at h D structural modules hTI hH
      (lt_of_le_of_ne hXY he) hY with hf | ⟨f,hf⟩
  · exact chosen_movement_of_quotient_rank_at h D structural hnone hTI hH
      (chosen_hstar_quotient_rank_of_generating_five_component_at h D structural hTI hH C hTX hf)
  · exact chosen_movement_of_rank_control_at h D structural hnone hTI
      (chosen_card_gt_four h D) hH
      (hstarRankControl_of_small_disjoint_at h D structural hTI hH
        (chosen_hstar_small_disjoint_of_alternating_action_at h D structural hTI hH hs f hf))

/-- The solvable branch now supplies the marked natural action without
an extra movement premise. -/
theorem natural_action_of_solvable_hstar_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) :
    ∃ d, (3 ≤ d ∧ d ≤ 5) ∧ Chapter6.Source.IsConjugationModel L V
      (Representation.specialLinearNatural (k := ZMod 2) d) :=
  natural_action_of_solvable_movement h D structural modules hnone hTI hH hs
    (chosen_movement_of_quotient_rank_at h D structural hnone hTI hH
      (chosen_hstar_quotient_rank_of_solvable_at h D structural hTI hH hs))

/-- Guarded natural recognition now retains only the nonsolvable exclusion.
Its proof and the final source assembly stay with qt-d-12213-hstar-natural. -/
theorem naturalLocalAnalysis_of_many_and_hstar_solvable_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (solvableStep : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      ¬ V ≤ H.pCoreIn 2 → Group.IsSolvable H) :
    ∃ d, NaturalLocalAnalysis T L V d := by
  have hm := fun H hH => chosen_hstar_movement_of_many_at h D structural modules hmany hnone hTI (H := H) hH
  have hs := fun H hH => solvableStep H hH (hm H hH)
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (D.rankOne_hasMaximalOutside_of_many h.toHypothesis1221 hmany)
  obtain ⟨d,hd,ha⟩ := natural_action_of_solvable_hstar_at h D structural modules hnone hTI hH (hs H hH)
  exact ⟨d,hd,ha,⟨H,hH⟩,hs,hm⟩

/-- Application to the original split-configuration consumer, with the H-star
rank obligation discharged. The nonsolvable, cyclic and rigidity branches
retain their existing final assembly owners. -/
theorem localConfiguration_of_many_and_hstar_solvable_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (solvableStep : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      ¬ V ≤ H.pCoreIn 2 → Group.IsSolvable H)
    (cyclicStep : ∀ d, NaturalLocalAnalysis T L V d →
      NoEscape L V → IsTISubgroup V → ∃ H P U, CyclicLocalAnalysis T L V d H P U)
    (rigidityStep : ∀ d H P U, NaturalLocalAnalysis T L V d →
      CyclicLocalAnalysis T L V d H P U → NoEscape L V → IsTISubgroup V →
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U) : ∃ d, SplitLinearConfiguration L V d := by
  apply localConfiguration_of_source_steps D
    (fun hn ht => naturalLocalAnalysis_of_many_and_hstar_solvable_at h D structural modules
      hmany hn ht solvableStep) cyclicStep rigidityStep hnone hTI


end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
