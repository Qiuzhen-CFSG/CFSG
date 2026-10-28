module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.Parameters
public import Theory.AtlasPort.LinearGroups.G2.DerivedParabolicGeneration

/-!
# Generation by the pulled-back G₂ parabolics

The two restricted parabolics generate the actual derived model, including
G₂(2)′. Pullback through the model map then proves generation of the component,
retaining its entire central kernel. Adjoining the supplied Sylow subgroup
gives generation of ⟨L,S⟩, even when S permutes components.

Source: Aschbacher–Smith, proof of 2.3.9(7), printed p.526.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

open Subgroup Atlas.G2.LieParabolicSetup

export Atlas.G2.DerivedParabolicGeneration
  (binary_restricted_pair_generate restricted_parabolics_generate)

namespace ParabolicCoordinates

variable {G : Type*} [Group G] {L S : Subgroup G} (d : ParabolicCoordinates L S)

/-- Both pulled-back parabolics generate L, including the binary derived case. -/
theorem first_sup_second : d.first ⊔ d.second = L := by
  have hc (P : Subgroup (Atlas.G2.Model d.field)) :
      (P ⊓ commutator (Atlas.G2.Model d.field)).comap d.modelMap = P.comap d.modelMap := by
    rw [comap_inf, ← d.model_range, MonoidHom.comap_range_self, inf_top_eq]
  have hgen : (parabolic₁.comap d.modelMap) ⊔ (parabolic₂.comap d.modelMap) = ⊤ := by
    rw [← hc parabolic₁, ← hc parabolic₂,
      comap_sup_eq_of_le_range d.modelMap (d.model_range.symm ▸ inf_le_right)
        (d.model_range.symm ▸ inf_le_right), restricted_parabolics_generate,
      ← d.model_range, MonoidHom.comap_range_self]
  rw [first, second, ← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map, range_subtype]

/-- Generation survives adjoining all of S, which may permute the components. -/
theorem overgroups_sup : d.firstOvergroup ⊔ d.secondOvergroup = L ⊔ S := by
  change (d.first ⊔ S) ⊔ (d.second ⊔ S) = L ⊔ S
  rw [sup_sup_sup_comm, sup_idem, d.first_sup_second]

theorem le_overgroups_sup : L ≤ d.firstOvergroup ⊔ d.secondOvergroup := by
  rw [d.overgroups_sup]
  exact le_sup_left

end ParabolicCoordinates

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

end
