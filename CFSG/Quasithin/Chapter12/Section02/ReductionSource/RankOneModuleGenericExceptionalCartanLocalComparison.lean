module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalComparison
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The Chapter 12 Cartan cubic comparison

The universal input adapter preserves the original chosen module and Sylow.
The original four-dimensional right action forces the natural-left Thompson
containment and Borel normalization. The final application constructs that
right action using the proved FF reduction and six-space obstruction on the
centralizing-cubic branch. No block or classification conclusion is assumed.

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

/-- Both literal Thompson comparisons in the four-space case, at every degree. -/
theorem rankOne_local_cartan_four_cubic_comparison
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (a : LocalA7Configuration T L H X K)
    (c : CartanPair T L H A B) (d : LocalCartanWitness T H A Y X C)
    (hc : Nat.card (localOmegaModule T K) = 16) :
    B ⊔ C ⊔ (T : Subgroup G) ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      Chapter6.Source.RankOneGeneric.localBorel T L ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  exact ⟨a.four_cubic_normalizes_thompson hi hH hgen c d hc,
    a.four_left_thompson_natural hi hH hgen c d hc⟩

/-- Original Chapter 12 inputs supply both comparisons on the centralizing-cubic branch. -/
theorem rankOne_local_cartan_noncentral_cubic_comparison
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (hXC : ¬ X ≤ omegaCentralizer T)
    (hd : C ≤ omegaCentralizer T) :
    ∃ K : Subgroup G, LocalA7Configuration T L H X K ∧
      Nat.card (localOmegaModule T K) = 16 ∧
      B ⊔ C ⊔ (T : Subgroup G) ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      Chapter6.Source.RankOneGeneric.localBorel T L ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
  localCartan_noncentral_cubic_thompson_comparison
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d hXC hd
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
