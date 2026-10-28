module
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# Sylow promotion through a normalizer-controlled subgroup

A two-subgroup P of H is Sylow if its normalizer preserves a nontrivial
subgroup E of P and each H-centralizer of a nonidentity element of E lies
in P. A larger two-normalizer would have a nontrivial central element in
its normal subgroup E, forcing that normalizer back into P. The finite
two-group normalizer condition then excludes every larger two-overgroup.

This isolates the normalizer argument used in Parrott (1972), printed
p.683, observation (i), and Aschbacher, *Finite Group Theory*, 47.1.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Normalizer stability and centralizer containment promote a two-subgroup to Sylow. -/
theorem exists_sylow_of_normalizer_control_and_centralizers
    (H P E : Subgroup G) (hP : IsPGroup 2 P) (hPH : P ≤ H)
    (hEP : E ≤ P) (hE : E ≠ ⊥)
    (hn : normalizer (P : Set G) ≤ normalizer (E : Set G))
    (hc : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set G) ≤ P) :
    ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = P := by
  have hmax (U : Subgroup G) (hU : IsPGroup 2 U) (hPU : P ≤ U)
      (hUH : U ≤ H) (hUN : U ≤ normalizer (P : Set G)) : U = P := by
    have hEU : E ≤ U := hEP.trans hPU
    let : (E.subgroupOf U).Normal :=
      (normal_subgroupOf_iff_le_normalizer hEU).mpr (hUN.trans hn)
    have hne : E.subgroupOf U ≠ ⊥ := by
      intro hh
      apply hE
      rw [← map_subgroupOf_eq_of_le hEU, hh, Subgroup.map_bot]
    obtain ⟨e, he, he1⟩ := (center U ⊓ E.subgroupOf U).bot_or_exists_ne_one.resolve_left
      (center_inf_ne_bot_of_normal hU _ hne)
    have he1G : (e : G) ≠ 1 := fun hh => he1 (Subtype.ext hh)
    apply le_antisymm _ hPU
    intro u hu
    exact hc e he.2 he1G ⟨hUH hu, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp he.1 ⟨u, hu⟩))⟩
  obtain ⟨S, hPS⟩ := (hP.comap_subtype (K := H)).exists_le_sylow
  let U := (S : Subgroup H).map H.subtype
  have hPU : P ≤ U := by
    rw [← map_subgroupOf_eq_of_le hPH]
    exact map_mono hPS
  exact ⟨S, prime_overgroup_eq_of_normalizer_control P H (normalizer (P : Set G))
    le_rfl hmax U (S.isPGroup'.map H.subtype) hPU (map_subtype_le _)⟩
end Subgroup
