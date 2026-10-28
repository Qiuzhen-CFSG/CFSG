module
public import Theory.GroupTheory.NormalClosureCentralizerCore

/-!
# Centralizers of Sylow-central seeds at prime index

A Sylow subgroup of prime index is maximal. If it centralizes a seed
which is not central in the whole group, it is the full seed centralizer.
The centralizer of the seed's normal closure is consequently the p-core.
No finiteness beyond the finite index is needed.

Source application: Aschbacher--Smith, original 15.2.6--8,
printed pp.1109--1110: the chosen module in the index-five parabolic YT.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A Sylow-central seed at prime index has core centralizer as soon as
its normal closure is not central. -/
theorem centralizer_normalClosure_eq_core_of_prime_index
    {p q : ℕ} [Fact p.Prime] (S : Sylow p G) (Z : Subgroup G)
    (hi : (S : Subgroup G).index = q) (hq : q.Prime)
    (hSZ : (S : Subgroup G) ≤ centralizer (Z : Set G))
    (hne : ¬ Z ≤ center G) :
    centralizer (normalClosure (Z : Set G) : Set G) = pCore p G := by
  have hmax : IsCoatom (S : Subgroup G) := by
    refine ⟨fun ht => ?_, fun B hSB => ?_⟩
    · have hone : q = 1 := hi.symm.trans (by simp [ht])
      exact hq.ne_one hone
    · have hm := relIndex_mul_index hSB.le
      rw [hi] at hm
      have hp : ((S : Subgroup G).relIndex B * B.index).Prime := hm ▸ hq
      rcases Nat.prime_mul_iff.mp hp with ⟨_,hB⟩ | ⟨_,hrel⟩
      · exact index_eq_one.mp hB
      · exact (hSB.not_ge (relIndex_eq_one.mp hrel)).elim
  have hc : centralizer (Z : Set G) = (S : Subgroup G) := by
    rcases hmax.le_iff.mp hSZ with ht | he
    · exact (hne (centralizer_eq_top_iff_subset.mp ht)).elim
    · exact he
  exact centralizer_normalClosure_eq_pCore_of_eq_sylow S Z hc
end Theory.GroupTheory
