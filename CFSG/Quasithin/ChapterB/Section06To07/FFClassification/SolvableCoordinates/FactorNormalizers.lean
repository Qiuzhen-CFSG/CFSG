module
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.SmallAction

/-!
# Normalizers of the two original solvable factors

When the natural product layer is self-centralizing, its factor-permutation
kernel is the layer itself. A permutation of two factors fixing either
factor is identity; hence each factor has exactly the layer as normalizer.
The original outside-group application pulls this identity through its
literal centralizer quotient to identify N_T(Hᵢ).
Source: Aschbacher–Smith E.2.3 and13.2.11(4), pp.216–217 and881.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G W} (c : SolvableFFFactors ρ)

theorem factor_normalizer_eq_of_two (hc : c.count = 2)
    (hcent : centralizer (offenderSubgroup ρ : Set G) = ⊥) (i : Fin c.count) :
    normalizer (c.factor i : Set G) = offenderSubgroup ρ := by
  apply le_antisymm
  · intro g hg
    have hfix : c.factorConjugation g i = i := c.factor_injective
      ((c.factor_map_conj g i).symm.trans (mem_normalizer_iff_map_conj_eq.mp hg))
    have hperm : ∀ (p : Equiv.Perm (Fin c.count)) (j : Fin c.count), p j = j → p = 1 := by
      rw [hc]
      decide
    have hk : g ∈ c.factorConjugation.ker := hperm _ i hfix
    rwa [c.factorConjugation_ker_eq_of_centralizer_eq_bot hcent] at hk
  · exact (normal_subgroupOf_iff_le_normalizer (c.factor_le_offenderSubgroup i)).mp
      (c.factor_normal_in_offenderSubgroup i)
end CFSG.Quasithin.ChapterB.SolvableFFFactors
