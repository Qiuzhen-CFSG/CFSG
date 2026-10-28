module
public import Theory.GroupTheory.SolvableSylowSupplement

/-!
# Containment from the residual and solvable Sylow overgroups

The normalizer of the Sylow intersection with the solvable residual is a
solvable supplement containing the prescribed Sylow two-subgroup. Therefore
control of that residual and all solvable overgroups of the same Sylow
controls the whole subgroup, with its ambient embedding retained.

Source application: Aschbacher--Smith 8.3.7, printed pp.724--725.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Contain a subgroup by controlling its residual and its solvable
overgroups of the prescribed Sylow two-subgroup. -/
theorem subgroup_le_of_residual_and_solvable_sylow_overgroups
    (H M : Subgroup G) (S : Sylow 2 H)
    (hR : (solvableResidual H).map H.subtype ≤ M)
    (hsolv : ∀ A : Subgroup G, A ≤ H → (S : Subgroup H).map H.subtype ≤ A →
      Group.IsSolvable A → A ≤ M) : H ≤ M := by
  obtain ⟨N,hN,hSN,hgen⟩ := exists_solvable_sylow_supplement S
  let := hN
  have hNM : N.map H.subtype ≤ M := hsolv _ (map_subtype_le _)
    (map_mono hSN) (Group.isSolvable_of_surjective (H.subtype.subgroupMap_surjective N))
  have hh := congrArg (Subgroup.map H.subtype) hgen
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
  rw [←hh]
  exact sup_le hNM hR
end Theory.GroupTheory
