module

public import CFSG.Quasithin.Chapter15.Section01.NormalizerSource
public import CFSG.Quasithin.Chapter15.Section01.MinimalParabolicSource
public import CFSG.Quasithin.ChapterD.Section01.Configuration

/-!
# Original selected-source reduction for 15.1.3

The proved 14.1.12 chooses the actual ordering maximum M_f outside M_c.
For every minimal local overgroup H outside M_f, the normalizer of
C_T(V(M_f)) gives the original qrc configuration and a generated group
with trivial two-core. The noncentral Thompson action gives either the
literal rank-two setup or the full orthogonal action on V(M_f).

The remaining branch centralizes V(M_f) and has the full Baumann control
used in 15.1.9. Its subsequent exclusion, the rank-two classification,
and the orthogonal analysis retain their own source proofs. This reduction
does not assume any of those three conclusions or choose an abstract action
in place of the original one.

Source: Aschbacher--Smith 14.1.12, p.979; 15.1.1, 15.1.3 and the start of
15.1.9, printed pp.1083--1088.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterB
open Chapter14.SourcePreliminaries Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- Select the actual M_f and construct the initial source alternatives.
Every auxiliary configuration uses that same chosen maximal local group. -/
theorem source_selected_reduction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∃ M : Subgroup G, IsOrderingMaximal T M ∧ M ≠ Mc ∧
      (∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
        ChapterD.QRCConfiguration (sourceNormalizer T M) H (T : Subgroup G)
          (localModule T M) ∧
        pCore 2 (sourceNormalizer T M ⊔ H : Subgroup G) = ⊥) ∧
      ((Nat.card (localModule T M) = 4 ∧
        Nonempty ((M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
          Equiv.Perm (Fin 3)) ∧
        RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M) ∨
      Nonempty (NaturalOrthogonalAction M (localModule T M)) ∨
      (elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) ∧
        localModule T M ≤ thompsonAlpha (T : Subgroup G) ∧
        baumann (T : Subgroup G) =
          baumann ((T : Subgroup G) ⊓ centralizer (localModule T M : Set G)) ∧
        (baumann (T : Subgroup G)).characteristicNormalizerClosure ≤ M ∧
        ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
          ChapterB.IsMinimalParabolicOver T H ∧
          IsSQTK KnownSimple.IsKnownSimple H ∧ generalizedFitting H = pCore 2 H)) := by
  obtain ⟨D, hD, M, hM, hne, hmax, hBaum, hdom, hoff, hall, hC⟩ :=
    UniformControl.source_lemma_14_1_12_selection hG T hempty hu hmany
  refine ⟨M, hmax, hne, ?_, ?_⟩
  · intro H hH
    exact ⟨source_15_1_1_qrcConfiguration hG T hmax hH,
      sourceNormalizer_join_twoCore_eq_bot T hmax hH⟩
  · by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (localModule T M : Set G)
    · obtain ⟨hVE, hB, _, hcontrol, _⟩ :=
        source_centralizing_baumann_control hG T hmax hJ
      refine Or.inr (Or.inr ⟨hJ, hVE, hB, hcontrol, ?_⟩)
      intro H hH
      obtain ⟨hP, _, _, hs, hc⟩ := source_centralizing_minimalParabolic hG T hmax hJ H hH
      exact ⟨hP, hs, hc⟩
    · rcases source_noncentral_rankTwo_or_orthogonal hG T hempty hmax hu hmany hne hJ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

/- The selected source QRC configurations have the non-normalization conclusion
   used by the first D-section alternatives. -/
theorem source_selected_reduction_nonNormalized
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∃ M : Subgroup G, IsOrderingMaximal T M ∧ M ≠ Mc ∧
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
        ¬ H ≤ normalizer (localModule T M : Set G) := by
  obtain ⟨M, hM, hne, hqrc, _⟩ := source_selected_reduction hG T hempty hu hmany
  refine ⟨M, hM, hne, ?_⟩
  intro H hH
  have hV : localModule T M ≠ ⊥ := by
    intro hz
    have hZ : centralInvolutions T ≤ localModule T M := le_conjugateSpanBy _ _
    have hmax : M ∈ maximalTwoLocalOvergroups (T : Subgroup G) :=
      ⟨hM.1.1, hM.1.2⟩
    exact centralInvolutions_ne_bot_of_maximal_local T hmax
      (bot_unique (hZ.trans_eq hz))
  exact ChapterD.QRCConfiguration.module_not_normalized_right (hqrc H hH).1 hV

end CFSG.Quasithin.Chapter15.Section01
