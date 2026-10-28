module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
/-!
# Recovering a subgroup normalizer from its image centralizer

If P≤T contains the kernel inside T, and its image is the centralizer
inside the image of T of a normal subgroup, every normalizer of T also
normalizes P. Intersecting the inverse image with T recovers P exactly.
This is the quotient normal-component reduction in Aschbacher–Smith
C.5.12, printed p.163.
-/
public section
namespace Subgroup
/-- Recover normalizer control from a normal image and the exact kernel bound. -/
theorem normalizer_le_of_image_centralizer {G H : Type*} [Group G] [Group H] (f : G →* H)
    (T P : Subgroup G) (hPT : P ≤ T) (hk : T ⊓ f.ker ≤ P)
    (L : Subgroup H) [L.Normal]
    (he : P.map f = T.map f ⊓ centralizer (L : Set H)) :
    normalizer (T : Set G) ≤ normalizer (P : Set G) := by
  have hi : T ⊓ (P.map f).comap f = P := by
    rw [comap_map_eq]
    apply le_antisymm
    · rintro t ⟨ht,hp⟩
      obtain ⟨p,hpP,k,hk',rfl⟩ := mem_sup_of_normal_right.mp hp
      have hkt : k ∈ T := by
        have h := T.mul_mem (T.inv_mem (hPT hpP)) ht
        simpa using h
      exact P.mul_mem hpP (hk ⟨hkt,hk'⟩)
    · exact le_inf hPT le_sup_left
  have hmap : (normalizer (T : Set G)).map f ≤ normalizer (P.map f : Set H) := by
    rw [he]
    apply (le_inf (T.le_normalizer_map f) ?_).trans inf_normalizer_le_normalizer_inf
    exact le_normalizer_of_normal
  have hpre : normalizer (T : Set G) ≤ normalizer ((P.map f).comap f : Set G) :=
    (map_le_iff_le_comap.mp hmap).trans (le_normalizer_comap f)
  rw [← hi]
  exact (le_inf le_rfl hpre).trans inf_normalizer_le_normalizer_inf
end Subgroup
