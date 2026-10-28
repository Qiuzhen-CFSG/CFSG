module

public import Theory.GroupTheory.Fitting.Core

/-!
# Isomorphisms of Fitting subgroups

An isomorphism sends each normal nilpotent subgroup to a normal nilpotent
subgroup. Applying this in both directions identifies the full Fitting
subgroups. This supports transport of the original Fitting actions.
-/

public section
open Subgroup
namespace Subgroup

private theorem fitting_map_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  apply map_le_iff_le_comap.mp
  let := hnil
  exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩

/-- Isomorphisms carry the full Fitting subgroup onto the full Fitting subgroup. -/
theorem map_fitting_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom = fittingSubgroup B := by
  apply le_antisymm (fitting_map_le e)
  have h := map_mono (f := e.toMonoidHom) (fitting_map_le e.symm)
  simpa [map_map] using h

end Subgroup
