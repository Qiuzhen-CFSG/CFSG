module

public import Theory.GroupTheory.SmallMoverFamily

/-!
# Normalization of the maximum-small-mover join

Simultaneous normalizers of the module, kernel and actor preserve the
maximum-small-mover family and its join. For a surjective quotient with
normal module and kernel contained in the actor, the normalizer of the
actor image therefore normalizes the join image.

The proof transports the family by conjugation and lifts quotient
normalizers through the full kernel. Source application: MS93 (5.1),
printed p.913, on the minimum characteristic replacement.
-/

public section
open Subgroup
namespace Subgroup.SmallMover
variable {G : Type*} [Group G]

theorem normalizer_join (U Q T : Subgroup G) (n : ℕ) :
    normalizer (U : Set G) ⊓ normalizer (Q : Set G) ⊓ normalizer (T : Set G) ≤
      normalizer (join U Q T n : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [join_map _ (MulAut.conj g).injective,
    mem_normalizer_iff_map_conj_eq.mp hg.1.1,
    mem_normalizer_iff_map_conj_eq.mp hg.1.2,
    mem_normalizer_iff_map_conj_eq.mp hg.2]
end Subgroup.SmallMover

namespace Subgroup.SmallMover
variable {G D : Type*} [Group G] [Group D]

theorem normalizer_image_le_normalizer_join_image
    (U T : Subgroup G) [U.Normal] (q : G →* D) (hq : Function.Surjective q)
    (hkT : q.ker ≤ T) (n : ℕ) :
    normalizer (T.map q : Set D) ≤ normalizer ((join U q.ker T n).map q : Set D) := by
  intro y hy
  obtain ⟨x,rfl⟩ := hq y
  have hxT : x ∈ normalizer (T : Set G) := by
    have hh := (T.map q).le_normalizer_comap q hy
    rwa [comap_map_eq_self hkT] at hh
  have hx := normalizer_join U q.ker T n
    ⟨⟨le_normalizer_of_normal (mem_top x),le_normalizer_of_normal (mem_top x)⟩,hxT⟩
  exact le_normalizer_map q (mem_map_of_mem q hx)
end Subgroup.SmallMover
