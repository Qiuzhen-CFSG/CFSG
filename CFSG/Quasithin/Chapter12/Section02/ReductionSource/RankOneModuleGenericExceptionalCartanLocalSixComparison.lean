module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSixComparison
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The original Chapter 12 six-space Thompson comparison

The universal Input adapter uses the original Sylow and canonical whole
reduced module. In the
right six-space the actual escaping cubic fails to normalize J(T), forcing
the left symmetric-five row and degree two. The original source inputs
therefore select the four-space at larger degree using the completed FF
reduction. No omega-centralization or block exclusion is assumed.

Source: Aschbacher–Smith 5.1.13 and 12.2.2, printed pp.637,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y X C K : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The six-space determines the original left degree, quotient and Cartan. -/
theorem rankOne_local_cartan_six_thompson_comparison
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (a : LocalA7Configuration T L H X K)
    (c : CartanPair T L H A B) (d : LocalCartanWitness T H A Y X C)
    (hc : Nat.card (localOmegaModule T K) = 64) :
    n = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) ∧
      A = C ∧ ¬ C ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
  a.six_left_symmetric_five
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c d hc

/-- The actual noncentral Chapter 12 inputs select the four-space above degree two. -/
theorem rankOne_local_cartan_noncentral_four_of_degree_gt_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 2 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K : Subgroup G, LocalA7Configuration T L H X K ∧
      Nat.card (localOmegaModule T K) = 16 ∧
      B ⊔ C ⊔ (T : Subgroup G) ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      Chapter6.Source.RankOneGeneric.localBorel T L ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany (by omega) hpsl
  obtain ⟨K,a⟩ := localCartan_ffReduction T L _ n hi H hH hgen A B c Y hY X C d hXC
  exact ⟨K,a,a.four_of_degree_gt_two hi hH hgen c d hn⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
