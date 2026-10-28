module
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Normal subgroups with full image modulo a solvable kernel

A normal subgroup of a perfect group is the whole group if its image modulo
a solvable kernel is full. Its quotient is both perfect and a solvable image
of that kernel, hence trivial. This lifts quotient commutator generation in
Aschbacher--Smith, Lemma 12.6.7, printed p.824.
-/

public section
open Subgroup
namespace Subgroup
theorem eq_top_of_perfect_of_solvable_kernel_image
    {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
    (f : A →* B) [Group.IsSolvable f.ker]
    (N : Subgroup A) [N.Normal] (himage : N.map f = ⊤) : N = ⊤ := by
  have hgen : N ⊔ f.ker = ⊤ := by
    have hh := congrArg (Subgroup.comap f) himage
    simpa only [comap_map_eq,comap_top] using hh
  let q := QuotientGroup.mk' N
  have hq : Function.Surjective (q.comp f.ker.subtype) := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N x
    have hg : g ∈ N ⊔ f.ker := hgen ▸ mem_top g
    obtain ⟨n,hn,k,hk,rfl⟩ := mem_sup_of_normal_left.mp hg
    refine ⟨⟨k,hk⟩,?_⟩
    change q k = q (n*k)
    rw [map_mul,show q n = 1 from (QuotientGroup.eq_one_iff n).mpr hn,one_mul]
  let : Group.IsSolvable (A ⧸ N) := Group.isSolvable_of_surjective hq
  exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N)

end Subgroup
