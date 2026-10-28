module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceGeometry

/-!
# The actual conjugation action on the cubic component

Ambient conjugation preserves the original point–line incidence and its
collinearity graph. The elements carrying W into its own connected
component form the actual component stabilizer. It contains every point
normalizer belonging to that component, as well as N(V).

Source: Aschbacher, *Sporadic Groups* (1994), the graph action in45.10–45.11,
pp.247–249. This module does not assume global connectedness.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

def conjugationGraphIso (g : G) : c.collinearity ≃g c.collinearity where
  toEquiv := {
    toFun := fun U => c.conjugatePoint U g
    invFun := fun U => c.conjugatePoint U g⁻¹
    left_inv := fun U => Subtype.ext (conjBy_inv _ _)
    right_inv := fun U => Subtype.ext (conjBy_inv' _ _) }
  map_rel_iff' := by
    intro U U'
    constructor
    · intro hh
      have hi := c.neighbor_conjugate hh g⁻¹
      change (U'.val.conjBy g).conjBy g⁻¹ ∈ c.neighbors ((U.val.conjBy g).conjBy g⁻¹) at hi
      change U'.val ∈ c.neighbors U.val
      simpa only [conjBy_inv] using hi
    · exact fun hh => c.neighbor_conjugate hh g

theorem reachable_conjugate {U U' : c.points} (hh : c.collinearity.Reachable U U') (g : G) :
    c.collinearity.Reachable (c.conjugatePoint U g) (c.conjugatePoint U' g) :=
  hh.map (c.conjugationGraphIso g).toHom

/-- Actual ambient conjugation on the original source points. -/
@[instance_reducible] def conjugationAction : MulAction G c.points where
  smul g U := c.conjugatePoint U g
  one_smul U := Subtype.ext (conjBy_one U.val)
  mul_smul g g' U := Subtype.ext (conjBy_conjBy U.val g' g).symm

/-- The subgroup stabilizing the component containing the original point W. -/
def componentStabilizer : Subgroup G where
  carrier := {g | c.collinearity.Reachable ⟨c.W, c.point_mem⟩
    (c.conjugatePoint ⟨c.W, c.point_mem⟩ g)}
  one_mem' := by
    have he : c.conjugatePoint ⟨c.W, c.point_mem⟩ 1 = ⟨c.W, c.point_mem⟩ :=
      Subtype.ext (conjBy_one _)
    change c.collinearity.Reachable ⟨c.W, c.point_mem⟩ (c.conjugatePoint ⟨c.W, c.point_mem⟩ 1)
    rw [he]
  mul_mem' := by
    intro g g' hg hg'
    have hh := c.reachable_conjugate hg' g
    have he : c.conjugatePoint (c.conjugatePoint ⟨c.W, c.point_mem⟩ g') g =
        c.conjugatePoint ⟨c.W, c.point_mem⟩ (g * g') := Subtype.ext (conjBy_conjBy _ _ _)
    exact hg.trans (he ▸ hh)
  inv_mem' := by
    intro g hg
    have hh := c.reachable_conjugate hg g⁻¹
    have he : c.conjugatePoint (c.conjugatePoint ⟨c.W, c.point_mem⟩ g) g⁻¹ =
        ⟨c.W, c.point_mem⟩ := Subtype.ext (conjBy_inv _ _)
    exact (he ▸ hh).symm

theorem mem_componentStabilizer_iff (g : G) : g ∈ c.componentStabilizer ↔
    c.collinearity.Reachable ⟨c.W, c.point_mem⟩ (c.conjugatePoint ⟨c.W, c.point_mem⟩ g) :=
  Iff.rfl

theorem component_point_normalizer_le {U : c.points}
    (hU : c.collinearity.Reachable ⟨c.W, c.point_mem⟩ U) :
    normalizer (U.val : Set G) ≤ c.componentStabilizer := by
  intro g hg
  have he : c.conjugatePoint U g = U := Subtype.ext (mem_normalizer_iff_map_conj_eq.mp hg)
  have hh := c.reachable_conjugate hU g
  rw [he] at hh
  exact hU.trans hh.symm

theorem point_normalizer_le_componentStabilizer :
    normalizer (c.W : Set G) ≤ c.componentStabilizer :=
  c.component_point_normalizer_le (SimpleGraph.Reachable.refl _)

theorem kernel_normalizer_le_componentStabilizer [Finite G] :
    normalizer (c.V : Set G) ≤ c.componentStabilizer := by
  intro g hg
  have hw : c.W.conjBy g ≤ c.V :=
    (map_mono c.line_le_kernel).trans_eq (mem_normalizer_iff_map_conj_eq.mp hg)
  by_cases he : c.W.conjBy g = c.W
  · have hp : c.conjugatePoint ⟨c.W, c.point_mem⟩ g = ⟨c.W, c.point_mem⟩ := Subtype.ext he
    change c.collinearity.Reachable ⟨c.W, c.point_mem⟩ (c.conjugatePoint ⟨c.W, c.point_mem⟩ g)
    rw [hp]
  · exact (show c.collinearity.Adj ⟨c.W, c.point_mem⟩
        (c.conjugatePoint ⟨c.W, c.point_mem⟩ g) from
      ⟨c.point_conjugate_mem c.point_mem g, he, c.V, c.line_mem, c.line_le_kernel, hw⟩).reachable

theorem componentStabilizer_preserves {U : c.points}
    (hU : c.collinearity.Reachable ⟨c.W, c.point_mem⟩ U)
    {g : G} (hg : g ∈ c.componentStabilizer) :
    c.collinearity.Reachable ⟨c.W, c.point_mem⟩ (c.conjugatePoint U g) :=
  hg.trans (c.reachable_conjugate hU g)

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
