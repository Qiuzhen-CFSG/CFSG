module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LineClosure

/-!
# Radical intersections fix common neighbors

For a nonadjacent pair, the two joining lines through any common neighbor
are distinct. Both endpoint radicals fix their incident lines; consequently
their intersection fixes the intersection point of these two lines. Applying
this to the literal plane marker gives the first step of AS91 (5.7).

This proves fixation, not membership in the common neighbor's radical. The
latter implication still requires the native residue intersection argument
before the common-neighbor containment field of Input can be assembled.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (5.7), p.601,
DOI 10.1007/BF01232280.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

/-- Distinct joining lines through a common neighbor determine that neighbor.
Thus the literal intersection of endpoint radicals fixes every common neighbor. -/
theorem core_intersection_fixes_common_neighbor (x y u : Point a.P)
    (hne : x ≠ y) (hn : ¬ Adj a.L x y) (hxu : Adj a.L x u) (hyu : Adj a.L y u)
    (v : G) (hv : v ∈ coreAt a.P x ⊓ coreAt a.P y) : v • u = u := by
  obtain ⟨l,hxl,hul⟩ := hxu.2
  obtain ⟨k,hyk,huk⟩ := hyu.2
  have hvl : v • l = l := a.core_fixes_lines x ⟨v,hv.1⟩ l hxl
  have hvk : v • k = k := a.core_fixes_lines y ⟨v,hv.2⟩ k hyk
  have hvl' : OnLine a.L (v • u) l := by
    have hh := incident_smul v hul
    rw [hvl] at hh
    exact hh
  have hvk' : OnLine a.L (v • u) k := by
    have hh := incident_smul v huk
    rw [hvk] at hh
    exact hh
  by_contra hneq
  obtain ⟨m,_,hm⟩ := a.unique_line (v • u) u ⟨hneq,l,hvl',hul⟩
  have hlk : l = k := (hm l ⟨hvl',hul⟩).trans (hm k ⟨hvk',huk⟩).symm
  exact hn ⟨hne,l,hxl,hlk.symm ▸ hyk⟩

/-- The first step of AS91 (5.7), with its ambient plane marker. Membership
in the radical at u is the remaining native intersection step. -/
theorem marker_fixes_common_neighbor (x y : Point a.P) (π : Plane z)
    (hxy : DistanceTwo a.L x y) (hxπ : OnPlane a.P x π) (hyπ : OnPlane a.P y π)
    (u : Point a.P) (hxu : Adj a.L x u) (hyu : Adj a.L y u) : marker π • u = u :=
  a.core_intersection_fixes_common_neighbor x y u hxy.1 hxy.2.1 hxu hyu (marker π)
    ⟨(a.marker_mem_core π x).mpr hxπ,(a.marker_mem_core π y).mpr hyπ⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
