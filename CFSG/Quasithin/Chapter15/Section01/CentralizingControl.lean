module

public import CFSG.Quasithin.Chapter15.Section01.NaturalReduction
public import CFSG.Quasithin.Chapter14.Section01.BaumannReduction
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.ElementaryThompsonFrattini

/-!
# Baumann control in the remaining branch of 15.1.3

When J(T) centralizes V(M), source 14.1.2 places V(M) in Ω₁Z(J(T))
and identifies Baum(T) with Baum(C_T(V(M))). The actual Sylow Frattini
argument and A.5.7 make N_M(C_T(V(M))) a uniqueness subgroup. It
normalizes the same Baumann subgroup, so every characteristic normalizer
lies in M. The normalizers of Baum(T), J(T), and T consequently lie in M.

The final application combines this control with the preceding natural
action reduction. The only remaining case has exactly the centralizing
geometry used by 15.1.9(1),(5),(7); it is not a proof of its exclusion.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
14.1.2, p.976, and 15.1.9, pp.1088--1089.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterB
open Chapter14.SourcePreliminaries Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The complete Baumann-control implication used in source 15.1.9(1).
The ordinary and characteristic normalizers are kept distinct. -/
theorem source_centralizing_baumann_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G)) :
    localModule T M ≤ thompsonAlpha (T : Subgroup G) ∧
      baumann (T : Subgroup G) =
        baumann ((T : Subgroup G) ⊓ centralizer (localModule T M : Set G)) ∧
      maximalTwoLocalOvergroups (M ⊓ normalizer (baumann (T : Subgroup G) : Set G)) = {M} ∧
      (baumann (T : Subgroup G)).characteristicNormalizerClosure ≤ M ∧
      normalizer (baumann (T : Subgroup G) : Set G) ≤ M ∧
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ M ∧
      normalizer (T : Set G) ≤ M := by
  let V := localModule T M
  let R := (T : Subgroup G) ⊓ centralizer (V : Set G)
  let B := baumann (T : Subgroup G)
  have hH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1, hM.1.2⟩
  let := localModule_elementary_from_source hG T hH
  let := (localModule_reduced_from_source hG T hH).normal
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  obtain ⟨hVE, hB⟩ := Chapter14.Source.lemma_14_1_2_1 T M V hM.1.2
    (localModule_le T hM.1.2) (le_inf (hJT.trans hM.1.2) hJ)
  have hu := UniformControl.source_unique_overgroup_sylow_centralizer hG T hM V le_rfl
    (localModule_le T hM.1.2)
  have hNRB : normalizer (R : Set G) ≤ normalizer (B : Set G) := by
    rw [show B = baumann R from hB]
    exact normalizer_le_normalizer_baumann R
  have huniq (N : Subgroup G) (hN : IsMaximalTwoLocal N)
      (hMN : M ⊓ normalizer (R : Set G) ≤ N) : N = M := by
    have hn : N ∈ maximalTwoLocalOvergroups (M ⊓ normalizer (R : Set G)) := ⟨hN, hMN⟩
    rw [hu] at hn
    exact Set.mem_singleton_iff.mp hn
  have hcontrol : B.characteristicNormalizerClosure ≤ M :=
    characteristicNormalizerClosure_le_of_unique_maximalTwoLocal huniq
      (T.isPGroup'.to_le (show B ≤ (T : Subgroup G) from inf_le_left))
      (inf_le_right.trans hNRB)
  have hZJ : centralInvolutions T ≤ elementaryAbelianMaxJ (T : Subgroup G) := by
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp (omegaCenter_le_omegaCenter_maxJ _ hz)).1
  have hJn : elementaryAbelianMaxJ (T : Subgroup G) ≠ ⊥ := by
    intro he
    exact centralInvolutions_ne_bot_of_maximal_local T hM.1 (bot_unique (hZJ.trans_eq he))
  have hJB : elementaryAbelianMaxJ (T : Subgroup G) ≤ B := by
    refine le_inf hJT ?_
    intro j hj e he
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp he).2.2 j hj).symm
  have hBn : B ≠ ⊥ := fun he => hJn (bot_unique (hJB.trans_eq he))
  have hNB : normalizer (B : Set G) ≤ M :=
    (normalizer_le_characteristicNormalizerClosure_self B hBn).trans hcontrol
  refine ⟨hVE, hB, ?_, hcontrol, hNB,
    (normalizer_maxJ_le_characteristicNormalizerClosure _ B hJB inf_le_left hJn).trans hcontrol,
    (normalizer_le_normalizer_baumann _).trans hNB⟩
  ext N
  constructor
  · intro hN
    exact Set.mem_singleton_iff.mpr (huniq N hN.1 ((inf_le_inf_left M hNRB).trans hN.2))
  · rintro rfl
    exact ⟨hM.1.1, inf_le_left⟩

/-- Source 15.1.9(1) applies to the literal V selected in 15.1.4 as well
as V(M): every elementary submodule of V(M) has the same Baumann centralizer. -/
theorem source_submodule_baumann_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (W : Subgroup G) (hWV : W ≤ localModule T M) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) ∧
      W ≤ thompsonAlpha (T : Subgroup G) ∧
      baumann (T : Subgroup G) = baumann ((T : Subgroup G) ⊓ centralizer (W : Set G)) ∧
      (baumann (T : Subgroup G)).characteristicNormalizerClosure ≤ M := by
  have hH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1, hM.1.2⟩
  let := localModule_elementary_from_source hG T hH
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (inclusion hWV) (inclusion_injective hWV)
  obtain ⟨hVE, _, _, hcontrol, _⟩ := source_centralizing_baumann_control hG T hM hJ
  have hWJ := hJ.trans (centralizer_le hWV)
  have hET : thompsonAlpha (T : Subgroup G) ≤ (T : Subgroup G) := by
    have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
      sSup_le fun _ hA => hA.1
    intro x hx
    exact hJT ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
  exact ⟨hWJ, hWV.trans hVE,
    lemma_B_2_3_5 _ W (hWV.trans (hVE.trans hET)) hWJ, hcontrol⟩

end CFSG.Quasithin.Chapter15.Section01
