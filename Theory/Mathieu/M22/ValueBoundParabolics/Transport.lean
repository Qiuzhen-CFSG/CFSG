module

public import Theory.Mathieu.M22.ValueBoundParabolics
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.QuasithinBasic

/-!
# Transport of the generalized Fitting subgroup for local quotients

An isomorphism takes normal nilpotent subgroups and components to subgroups
of the same kind, hence takes their generated subgroup F* onto F*. This
gives an actual equivalence of the intrinsic generalized Fitting subgroups.
It allows the small symmetric quotient calculations to be applied to the
local pairs in E.4.3 without replacing a two-core by an assumed kernel.

Source: the intrinsic definition F* = F E; Aschbacher–Smith E.4.2–3,
printed pp. 241–242, combined manuscript of 1 March 2004.
-/

public section
namespace Sporadic.Mathieu.M22ValueBound
open Subgroup Theory.GroupTheory
variable {G K : Type*} [Group G] [Group K]

private theorem map_generalizedFitting_le (e : G ≃* K) :
    (generalizedFitting G).map e.toMonoidHom ≤ generalizedFitting K := by
  rw [generalizedFitting, Subgroup.map_sup]
  apply sup_le
  · apply (Subgroup.map_le_iff_le_comap).mpr
    apply sSup_le
    rintro N ⟨hn, hnil⟩
    apply (Subgroup.map_le_iff_le_comap).mp
    apply le_trans _ (fitting_le_generalizedFitting K)
    let := hnil
    exact le_sSup ⟨hn.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩
  · apply (Subgroup.map_le_iff_le_comap).mpr
    apply sSup_le
    intro N hn
    exact (Subgroup.map_le_iff_le_comap).mp
      (component_le_generalizedFitting K _ (hn.map_equiv e))

/-- The intrinsic generalized Fitting subgroup is invariant under isomorphism. -/
theorem map_generalizedFitting (e : G ≃* K) :
    (generalizedFitting G).map e.toMonoidHom = generalizedFitting K := by
  apply le_antisymm (map_generalizedFitting_le e)
  have h := Subgroup.map_mono (f := e.toMonoidHom) (map_generalizedFitting_le e.symm)
  have hi : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id K := by
    ext x
    exact e.apply_symm_apply x
  simpa only [Subgroup.map_map, hi, Subgroup.map_id] using h

/-- The restriction of the isomorphism to the actual generalized Fitting subgroups. -/
noncomputable def generalizedFittingEquiv (e : G ≃* K) :
    generalizedFitting G ≃* generalizedFitting K :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_generalizedFitting e))

end Sporadic.Mathieu.M22ValueBound
