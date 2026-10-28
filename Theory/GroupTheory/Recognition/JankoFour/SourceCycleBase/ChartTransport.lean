module

public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Input

/-!
# Stabilizers under the original Todd marking

Equivariance and injectivity of the native residue charts identify both
point-side overlaps with literal native stabilizers under the same quotient
map. Thus the interface retains marked incidence, not just abstract quotient
isomorphism types. No section 7 conclusion is used.

Source: AS91, opening of §§5 and 7 and (5.4).
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase

open Subgroup GraphUniquenessSystem LocalGeometry.LocalSubgroups
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {P : PointData z} {L : LineData z P}

namespace ResidueChart
variable (c : ResidueChart P L)

def baseLine : {l : Line L // OnLine L (Cosets.vertex P.M 1) l} :=
  ⟨Cosets.vertex L.G₂ 1, ⟨1, rfl, rfl⟩⟩

def basePlane : {π : Plane z // OnPlane P (Cosets.vertex P.M 1) π} :=
  ⟨Cosets.vertex (centralizer z) 1, ⟨1, rfl, rfl⟩⟩

theorem point_line_overlap :
    L.G₂.subgroupOf P.M = (trioStabilizer (c.lines baseLine)).comap P.projection := by
  ext m
  have hm : (m : G) • Cosets.vertex P.M 1 = Cosets.vertex P.M 1 := by
    simp [m.property]
  have hi := incident_smul (m : G) (show OnLine L (Cosets.vertex P.M 1)
    (Cosets.vertex L.G₂ 1) from ⟨1, rfl, rfl⟩)
  rw [hm] at hi
  let l' : {l : Line L // OnLine L (Cosets.vertex P.M 1) l} :=
    ⟨(m : G) • Cosets.vertex L.G₂ 1, hi⟩
  have he := c.lines_equivariant m baseLine l' rfl
  change (m : G) ∈ L.G₂ ↔ P.projection m • (c.lines baseLine).parts = (c.lines baseLine).parts
  rw [← he]
  constructor
  · intro h
    have hl : l' = baseLine := Subtype.ext (by
      simpa only [l', baseLine, Cosets.smul_vertex, mul_one] using
        (Cosets.vertex_eq_base L.G₂ (m : G)).mpr h)
    rw [hl]
  · intro h
    have hl : l' = baseLine := c.lines.injective (Native.line_parts_injective h)
    have hv := congrArg Subtype.val hl
    exact (Cosets.vertex_eq_base L.G₂ (m : G)).mp (by
      simpa only [l', baseLine, Cosets.smul_vertex, mul_one] using hv)

theorem point_plane_overlap :
    (centralizer z).subgroupOf P.M =
      (sextetStabilizer (c.planes basePlane)).comap P.projection := by
  ext m
  have hm : (m : G) • Cosets.vertex P.M 1 = Cosets.vertex P.M 1 := by
    simp [m.property]
  have hi := incident_smul (m : G) (show OnPlane P (Cosets.vertex P.M 1)
    (Cosets.vertex (centralizer z) 1) from ⟨1, rfl, rfl⟩)
  rw [hm] at hi
  let π' : {π : Plane z // OnPlane P (Cosets.vertex P.M 1) π} :=
    ⟨(m : G) • Cosets.vertex (centralizer z) 1, hi⟩
  have he := c.planes_equivariant m basePlane π' rfl
  change (m : G) ∈ centralizer z ↔
    P.projection m • (c.planes basePlane).parts = (c.planes basePlane).parts
  rw [← he]
  constructor
  · intro h
    have hp : π' = basePlane := Subtype.ext (by
      simpa only [π', basePlane, Cosets.smul_vertex, mul_one] using
        (Cosets.vertex_eq_base (centralizer z) (m : G)).mpr h)
    rw [hp]
  · intro h
    have hp : π' = basePlane := c.planes.injective (Native.plane_parts_injective h)
    have hv := congrArg Subtype.val hp
    exact (Cosets.vertex_eq_base (centralizer z) (m : G)).mp (by
      simpa only [π', basePlane, Cosets.smul_vertex, mul_one] using hv)

end ResidueChart
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
