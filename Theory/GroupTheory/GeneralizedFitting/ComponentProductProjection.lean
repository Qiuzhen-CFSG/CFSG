module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Components and solvable direct factors

A component of S × H, with S solvable, projects trivially to S because it
is perfect. Its projection to H is therefore injective, and its nontrivial
image remains a component. This supplies an actual group isomorphism, not
merely an identification of central quotients.

Source: the component calculus of GLS, vol. 2, Theorem 3.5; applied to the
centralizer products in Aschbacher–Smith 16.1.5 and 16.1.7, pp.1171–1172.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {S H : Type*} [Group S] [Group H]

/-- Projection away from a solvable direct factor identifies each component
with an actual component of the other factor. -/
theorem IsComponent.equiv_component_of_solvable_prod [Group.IsSolvable S]
    (K : Subgroup (S × H)) (hK : IsComponent (S × H) K) :
    ∃ L : Subgroup H, IsComponent H L ∧ Nonempty (K ≃* L) := by
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hf : K.map (MonoidHom.fst S H) = ⊥ := by
    let : Group.IsPerfect (K.map (MonoidHom.fst S H)) := Group.IsPerfect.map _
    by_contra hn
    let : Nontrivial (K.map (MonoidHom.fst S H)) := (nontrivial_iff_ne_bot _).mpr hn
    exact Group.IsPerfect.not_isSolvable (K.map (MonoidHom.fst S H)) inferInstance
  have hx (x : K) : (x : S × H).1 = 1 := by
    exact mem_bot.mp (hf ▸ mem_map_of_mem (MonoidHom.fst S H) x.property)
  let f : K →* H := (MonoidHom.snd S H).comp K.subtype
  have hfi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact Prod.ext ((hx x).trans (hx y).symm) he
  let L := K.map (MonoidHom.snd S H)
  have hL : IsComponent H L := by
    rcases hK.map_surjective (MonoidHom.snd S H) (fun y => ⟨(1, y), rfl⟩) with hb | hL
    · have hfr : f.range = ⊥ := by simpa only [f, MonoidHom.range_comp, range_subtype] using hb
      have htriv (x : K) : x = 1 := hfi (by
        rw [map_one]
        exact mem_bot.mp (hfr ▸ (show f x ∈ f.range from ⟨x, rfl⟩)))
      obtain ⟨x, y, hne⟩ := exists_pair_ne K
      exact (hne ((htriv x).trans (htriv y).symm)).elim
    · exact hL
  refine ⟨L, hL, ⟨?_⟩⟩
  exact (MonoidHom.ofInjective hfi).trans (MulEquiv.subgroupCongr (by
    simp only [f, L, MonoidHom.range_comp, range_subtype]))

end Theory.GroupTheory
