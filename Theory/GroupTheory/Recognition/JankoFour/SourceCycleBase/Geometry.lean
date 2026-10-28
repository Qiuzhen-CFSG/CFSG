module

public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Input

/-!
# First geometric consequences for the cycle argument

The unique joining line retains its actual incidence witnesses. The plane
marker has order two and acts nontrivially on the neighbor set of every point
of its plane. Regularity on the four other points of a line gives the unique
fixed-point assertion used in the final paragraph of (7.9).

For Δ₁² pairs we also prove the uniqueness clause of (7.5) and its lower bound
of three common neighbors on each line of the plane through the first point.
No connectedness of common-neighbor graphs is asserted here.

Source: AS91 (5.2)–(5.4), (6.1), (7.5.1), (7.5.3), and the end of (7.9).
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase

open Subgroup GraphUniquenessSystem
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

theorem lineType_smul {P : LocalGeometry.LocalSubgroups.PointData z}
    {L : LocalGeometry.LocalSubgroups.LineData z P} {c : ResidueChart P L}
    {i : Fin 5} {x : Point P} {l k : Line L}
    (g : G) (h : LineType c i x l k) : LineType c i (g • x) (g • l) (g • k) := by
  obtain ⟨r, a, b, rfl, rfl, rfl, hd⟩ := h
  exact ⟨g * r, a, b, rfl, mul_smul g r a.val, mul_smul g r b.val, hd⟩

theorem lineType_smul_iff {P : LocalGeometry.LocalSubgroups.PointData z}
    {L : LocalGeometry.LocalSubgroups.LineData z P} (c : ResidueChart P L)
    (i : Fin 5) (x : Point P) (l k : Line L) (g : G) :
    LineType c i (g • x) (g • l) (g • k) ↔ LineType c i x l k := by
  constructor
  · intro ht
    simpa only [inv_smul_smul] using lineType_smul g⁻¹ ht
  · exact lineType_smul g

namespace Input
variable (d : Input h)

noncomputable def joiningLine {x y : Point d.P} (hxy : Adj d.L x y) : Line d.L :=
  (d.unique_line x y hxy).choose

theorem joiningLine_incident {x y : Point d.P} (hxy : Adj d.L x y) :
    OnLine d.L x (d.joiningLine hxy) ∧ OnLine d.L y (d.joiningLine hxy) :=
  (d.unique_line x y hxy).choose_spec.1

theorem line_eq_of_incident {x y : Point d.P} (hne : x ≠ y) {l k : Line d.L}
    (hxl : OnLine d.L x l) (hyl : OnLine d.L y l)
    (hxk : OnLine d.L x k) (hyk : OnLine d.L y k) : l = k := by
  obtain ⟨m, _, hm⟩ := d.unique_line x y ⟨hne, l, hxl, hyl⟩
  exact (hm l ⟨hxl, hyl⟩).trans (hm k ⟨hxk, hyk⟩).symm

theorem core_fixes_point (x : Point d.P) (e : coreAt d.P x) : (e : G) • x = x :=
  coreAt_le_stabilizer d.P x e.property

theorem marker_order (h : IsTypeJ4 z) (π : Plane z) : orderOf (marker π) = 2 := by
  rw [← vertex_representative π, marker_vertex]
  change orderOf ((MulAut.conj (representative π)) z) = 2
  exact (orderOf_injective (MulAut.conj (representative π)).toMonoidHom
    (MulAut.conj (representative π)).injective z).trans h.involution

theorem marker_ne_one (h : IsTypeJ4 z) (π : Plane z) : marker π ≠ 1 := by
  intro he
  have ho := marker_order h π
  rw [he, orderOf_one] at ho
  contradiction

theorem marker_sq (h : IsTypeJ4 z) (π : Plane z) : marker π * marker π = 1 := by
  have hp := pow_orderOf_eq_one (marker π)
  rwa [marker_order h π, pow_two] at hp

theorem marker_fixes_point {π : Plane z} {x : Point d.P} (hx : OnPlane d.P x π) :
    marker π • x = x :=
  d.core_fixes_point x ⟨marker π, (d.marker_mem_core π x).mpr hx⟩

/-- Faithfulness is used on the whole neighbor set, not on all five points
of a single line. -/
theorem marker_moves_neighbor {π : Plane z} {x : Point d.P} (hx : OnPlane d.P x π) :
    ∃ y, Adj d.L x y ∧ marker π • y ≠ y := by
  classical
  by_contra hn
  push Not at hn
  exact marker_ne_one h π
    (d.core_faithful_neighbors x ⟨marker π, (d.marker_mem_core π x).mpr hx⟩ hn)

/-- The regular order-four image implies that a nontrivially acted-on line
has precisely its incident plane point fixed by the central involution. -/
theorem marker_unique_fixed_on_line {π : Plane z} {x w v : Point d.P} {l : Line d.L}
    (hxπ : OnPlane d.P x π) (hxl : OnLine d.L x l) (hwl : OnLine d.L w l)
    (hmove : marker π • w ≠ w) (hvl : OnLine d.L v l) :
    marker π • v = v ↔ v = x := by
  constructor
  · intro hv
    by_contra hvx
    exact hmove (d.core_regular_other x l hxl
      ⟨marker π, (d.marker_mem_core π x).mpr hxπ⟩ v hvl hvx hv w hwl)
  · rintro rfl
    exact d.marker_fixes_point hxπ

theorem planeDistanceTwo_unique_plane {x y : Point d.P} (hxy : PlaneDistanceTwo d.L x y) :
    ∃! π, OnPlane d.P x π ∧ OnPlane d.P y π := by
  obtain ⟨hd, π, hx, hy⟩ := hxy
  exact ⟨π, ⟨hx, hy⟩, fun σ hσ => d.unique_plane π x y hx hy hd.1 hd.2.1 σ hσ.1 hσ.2⟩

/-- The source lower bound in (7.5.3), on a line through x in the unique plane. -/
theorem three_le_common_neighbors_on_line {x y : Point d.P} {π : Plane z} {l : Line d.L}
    (hxy : DistanceTwo d.L x y) (_hxπ : OnPlane d.P x π) (hyπ : OnPlane d.P y π)
    (hxl : OnLine d.L x l) (hlπ : LineOnPlane d.L l π) :
    3 ≤ {u | Adj d.L x u ∧ Adj d.L y u ∧ OnLine d.L u l}.ncard := by
  obtain ⟨i, hi⟩ := d.plane_pair_types π y l hyπ hlπ
  have hnyx : ¬ Adj d.L y x := fun hh => hxy.2.1 (adj_symm hh)
  fin_cases i
  · exact (hxy.2.1 ⟨hxy.1, l, hxl, hi⟩).elim
  · exact (hnyx (hi x hxl)).elim
  · change {u | OnLine d.L u l ∧ Adj d.L y u}.ncard = 3 at hi
    rw [← hi]
    apply Set.ncard_le_ncard (ht := Set.toFinite _)
    intro u hu
    have hux : u ≠ x := by rintro rfl; exact hnyx hu.2
    exact ⟨⟨hux.symm, l, hxl, hu.1⟩, hu.2, hu.1⟩

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
