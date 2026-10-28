module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.Words
public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.FirstCentralizer

/-!
# The full binary Ree centralizer of the marked long-root involution

Conjugation by the full Borel preserves its intersection with the derived
group and hence fixes the unique nonidentity center element of that derived
Sylow subgroup. The derived centralizer is already the marked first Tits
parabolic. Both full overgroups contain an element outside the derived
subgroup, so its index two identifies the full centralizer with the first
Ree parabolic. Source: Aschbacher--Smith F.4.27(4)(i), printed p.288.
-/

public section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths
open Subgroup

private theorem sylow_action (g : ReeF4.Model 0) (hg : g ∈ S) :
    ExceptionalParabolics.S.map (atlasAction g).toMonoidHom = ExceptionalParabolics.S := by
  apply eq_of_le_of_card_ge
  · rintro y ⟨x, hx, rfl⟩
    apply (mem_map_iff_mem atlasEmbedding_injective).mp
    rw [atlas_sylow_map]
    refine ⟨?_, ?_⟩
    · change atlasEmbedding (atlasAction g x) ∈ S
      rw [atlasAction_apply]
      exact S.mul_mem (S.mul_mem hg (atlas_sylow_map_le (mem_map_of_mem _ hx))) (S.inv_mem hg)
    · rw [← atlasEmbedding_range]
      exact ⟨atlasAction g x, rfl⟩
  · rw [card_map_of_injective (atlasAction g).injective]

theorem sylow_centralizes_z : S ≤ centralizer {z} := by
  intro g hg
  rw [mem_centralizer_singleton_iff]
  have h := congrArg atlasEmbedding (RelativeParabolicNormalizers.fixes_r5
    (atlasAction g) (sylow_action g hg))
  rw [atlasAction_apply] at h
  exact mul_inv_eq_iff_eq_mul.mp h

private theorem derived_first_centralizes :
    ExceptionalParabolics.first.map atlasEmbedding ≤ centralizer {z} := by
  rintro x ⟨y, hy, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have h := mem_centralizer_singleton_iff.mp (ExceptionalParabolics.first_le_centralizer hy)
  exact (map_mul atlasEmbedding _ _).symm.trans ((congrArg atlasEmbedding h).trans
    (map_mul atlasEmbedding _ _))

private theorem centralizer_in_derived {x : ReeF4.Model 0}
    (hx : x ∈ commutator (ReeF4.Model 0)) (hc : x ∈ centralizer {z}) : x ∈ first := by
  rw [← atlasEmbedding_range] at hx
  obtain ⟨y, rfl⟩ := hx
  have hy : y ∈ ExceptionalParabolics.first := by
    rw [RelativeParabolicNormalizers.first_eq_centralizer, mem_centralizer_singleton_iff]
    apply atlasEmbedding_injective
    simpa only [map_mul, z] using mem_centralizer_singleton_iff.mp hc
  exact atlas_first_map_le (mem_map_of_mem _ hy)

private theorem sylow_not_le_derived : ¬ S ≤ commutator (ReeF4.Model 0) := by
  intro h
  have he : ExceptionalParabolics.S.map atlasEmbedding = S := by
    rw [atlas_sylow_map, inf_eq_left.mpr h]
  have hc := congrArg (fun H : Subgroup (ReeF4.Model 0) => Nat.card H) he
  rw [card_map_of_injective atlasEmbedding_injective, ExceptionalParabolics.sylow_card,
    sylow_card] at hc
  norm_num at hc

/-- The actual first full Ree parabolic is the full long-root centralizer. -/
theorem first_eq_centralizer_z : first = centralizer {z} := by
  obtain ⟨a, ha, hout⟩ := Set.not_subset.mp sylow_not_le_derived
  have haF := sylow_le_first ha
  have haC := sylow_centralizes_z ha
  have hainn : a⁻¹ ∉ commutator (ReeF4.Model 0) := by simpa using hout
  have hprod (x : ReeF4.Model 0) (hx : x ∉ commutator (ReeF4.Model 0)) :
      a⁻¹ * x ∈ commutator (ReeF4.Model 0) :=
    ((commutator (ReeF4.Model 0)).mul_mem_iff_of_index_two derived_index).mpr
      (iff_of_false hainn hx)
  apply le_antisymm
  · intro x hx
    by_cases hd : x ∈ commutator (ReeF4.Model 0)
    · apply derived_first_centralizes
      rw [atlas_first_map]
      exact ⟨hx, hd⟩
    · have hh : a⁻¹ * x ∈ centralizer {z} := by
        apply derived_first_centralizes
        rw [atlas_first_map]
        exact ⟨first.mul_mem (first.inv_mem haF) hx, hprod x hd⟩
      simpa only [mul_inv_cancel_left] using (centralizer {z}).mul_mem haC hh
  · intro x hx
    by_cases hd : x ∈ commutator (ReeF4.Model 0)
    · exact centralizer_in_derived hd hx
    · have hh := centralizer_in_derived (hprod x hd)
        ((centralizer {z}).mul_mem ((centralizer {z}).inv_mem haC) hx)
      simpa only [mul_inv_cancel_left] using first.mul_mem haF hh

end Tits.ExceptionalParabolics.FullRee.LongRootPaths
