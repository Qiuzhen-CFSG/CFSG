module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.Source
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.ConcreteFactors
/-!
# Genuine C.1.9 in the radical exclusion

The proved distinct-block theorem has exactly the original alternating-three
fitting guard used in 1.3.8. Its upper two-three core is definitionally the
same preimage, so it supplies the existing universal SourceC19 contract
without a new hypothesis. The concrete residual-factor consumer then removes
C.1.9 from the binary-block exclusion, retaining only its separate A.1.15
input. The characteristic-two guard is discharged by the existing global He
bridge inside that consumer.

Source: Aschbacher--Smith, C.1.9, printed p.123; proof of1.3.8, p.514.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.BlockRigidity
universe u

theorem sourceC19 : SourceC19.{u} := by
  intro D _ _ hguard A B hA hB hne
  exact ChapterC.blocks_commute hguard hA hB hne
end CFSG.Quasithin.Chapter1.RadicalExclusions.BlockRigidity

namespace CFSG.Quasithin.Chapter1.RadicalExclusions
open BlockRigidity
universe u
variable {G : Type u} [Group G] [Finite G]

theorem BinaryBlockEmbedding.false_of_sourceA115
    (h115 : SourceA115.{u})
    (T : Sylow 2 G) {p : ℕ} {X P L₀ M H₀ K : Subgroup G}
    (h : BinaryBlockEmbedding p T X P H₀ K)
    (hc : Configuration p T X P L₀ M)
    (hH : H₀ ∈ HOver G (T : Set G))
    (h114 : HOver G (T : Set G) ⊆ He G) : False := by
  obtain ⟨t, _, _, _, _, _, hpair, htrace⟩ :=
    h.concrete_factor_pair sourceC19 T hc hH h114 (h115 := h115)
  have hn : L₀ ≤ normalizer (X : Set G) := by
    rw [← hc.normalizer_radical, hc.normalizer_local]
    exact L₀.le_normalizer
  exact h.no_factor_pair hc _ _
    (fun d hd => (hpair d (hn hd)).imp And.left And.left) htrace
end CFSG.Quasithin.Chapter1.RadicalExclusions
