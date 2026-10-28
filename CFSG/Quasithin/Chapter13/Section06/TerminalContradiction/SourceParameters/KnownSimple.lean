module

public import CFSG.Quasithin.ChapterE.GenerationKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.ParabolicGeneration
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.TerminalConsumer
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup

/-!
# Original 13.6.25--26 with E-generation discharged

Every member of H(T,M) embeds into the two-local normalizer of its nontrivial
two-core and is therefore SQTK on the full KnownSimple catalogue. The proved
minimal-parabolic generation theorem supplies every witness required by the
13.6.25 transfer. The A5 coordinates compute the local module parameter.
Thus all four 13.6.25 conclusions and both 13.6.26 conclusions retain only
the genuine earlier A5 setup, A.3.8 and 13.3.8 source inputs.

The last theorem applies the actual generation bound to the first residual
construction of 13.6.27, preserving the original marked involution and
centralizer. No universal E.3.35 or parameter-attainment callback remains.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
13.6.25--27, printed pp.933--935.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
open _root_.CFSG.Quasithin.ChapterE
universe u
variable {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V M MV : Subgroup G} [IsElementaryAbelian 2 V]

theorem source_13_6_25_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (s : EarlierA5Setup T L V M MV) :
    (∀ i : ℕ, i = 0 ∨ i = 1 →
      indexedWeakClosure V (T : Subgroup G) i ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      Chapter3.NormalIn (indexedWeakClosure V (T : Subgroup G) i) (L ⊔ (T : Subgroup G))) ∧
    (∀ H ∈ Chapter1.HOutside G (T : Set G) (M : Set G), 1 < generationParameter H) ∧
    (∀ H ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable H → H ≤ M) ∧
    globalR V = 3 ∧ 1 < globalW V (T : Subgroup G) := by
  apply source_13_6_25_of_minimalParabolic_generation s s.localA_eq_one
  intro H hH P hP
  exact source_intrinsic_minimalParabolic_generation_knownSimple
    (Chapter1.RadicalExclusions.sqtk_of_mem_H hG hH.1.1) (T.subtype hH.1.2) P hP

theorem source_13_6_26_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA38 : EarlierA38Three.{u}) (s : EarlierA5Setup T L V M MV)
    (h1338 : Earlier1338Two T) (L₁ G₁ : Subgroup G) :
    ∀ H ∈ Chapter13.Section08.Source.Hz L₁ (T : Subgroup G) G₁ M,
      (∀ K ∈ Chapter1.cComponentsIn H, ¬ K ≤ M) ∧
      (∀ p : ℕ, p.Prime → 3 < p → O2p H p = Chapter13.Section08.Source.QH H) := by
  intro H hH
  refine ⟨source_13_6_26_1_of_A5_setup hG hA38 T L V M MV L₁ G₁ s hH, ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  exact source_13_6_26_2_of_solvable_source s s.localA_eq_one h1338 L₁ G₁ hH p hlarge

theorem exists_initial_residual_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (s : EarlierA5Setup T L V M MV)
    (hT : (T : Subgroup G) ≤ centralizer ({s.z.val} : Set G)) :
    ∃ H ∈ Chapter3.HStar (T : Subgroup G) M,
      H ≤ centralizer ({s.z.val} : Set G) ∧
      1 < generationParameter H ∧
      (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H ∧
      ¬ (pResidual 2 H).map H.subtype ≤ M ∧
      (T : Subgroup G) ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) := by
  have hz : orderOf s.z.val = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian s.z.val s.z.property)
      (fun h => s.z_nonidentity (Subtype.ext h))
  have hM : M ∈ maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) :=
    s.unique_overgroup.symm ▸ Set.mem_singleton M
  exact Components.exists_initial_residual T M s.z.val hz
    hT (le_sup_right.trans hM.2) s.singular_escape (source_13_6_25_knownSimple hG s).2.1
end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
