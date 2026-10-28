module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.LocalAdjacency
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.GraphComparison
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.Complement.LocalMap
/-!
# Uniqueness of the original cubic geometry and ambient group

The proved marked local normalizer isomorphism preserves the three orbit
stabilizers and all adjacency tests. Its equivariant point bijection is
therefore a graph isomorphism. Intrinsic root recovery then gives the
ambient group isomorphism. Every hypothesis is supplied by the two
original SourceConfiguration objects; no comparison premise is added.
Source: Aschbacher, Sporadic Groups (1994),45.11, pp.248–249.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)
variable {G' : Type*} [Group G'] [Finite G'] {z' : G'} {h' : IsType z'}
variable {P' : Sylow 3 (centralizer z')} (c' : SourceConfiguration h' P')

theorem exists_graph_iso : Nonempty (c.collinearity ≃g c'.collinearity) := by
  obtain ⟨L⟩ := c.exists_localMap c'
  obtain ⟨Y,hYL,hY,hne,-,hK⟩ := c.exists_complement_fixed_opposite_cubic
  obtain ⟨Y',hYL',hY',hne',-,hK'⟩ := c'.exists_complement_fixed_opposite_cubic
  have hamb (n:normalizer (c.W:Set G)) : L.ambient n=(L.equiv n).val := rfl
  have hI (n:normalizer (c.W:Set G)) :
      n.val∈normalizer (c.otherAxis:Set G) ↔ (L.equiv n).val∈normalizer (c'.otherAxis:Set G') := by
    simpa only [c.complement_inf_kernel_eq_otherAxis,c'.complement_inf_kernel_eq_otherAxis,hamb] using
      L.normalizes_axis_iff n
  obtain ⟨F,hFW,hFI,hFY,hact⟩ := c.marked_point_equiv c' L.equiv hI
    (fun n=>by simpa only [hamb] using (L.complement_mem_iff n).symm) hYL hY hne hK hYL' hY' hne' hK'
  refine ⟨{toEquiv:=F,map_rel_iff':=?_}⟩
  intro U V
  exact c.localMap_adj_iff c' L.equiv
    (fun n hn=>by simpa only [hamb] using (L.odd_mem_iff n).mpr hn) (fun n hn=>by simpa only [hamb] using (L.kernel_mem_iff n).mpr hn)
    (fun n hn=>by simpa only [hamb] using (L.normalizes_kernel_iff n).mp hn)
    (fun n hn=>by simpa only [hamb] using (L.exists_complement_conjugate_displacement_iff n).mp hn)
    hYL hY hne hK hYL' hY' hne' hK' F hFW hFI hFY hact U V

include c c' in
theorem exists_group_equiv : Nonempty (G≃*G') := by
  obtain ⟨F⟩ := c.exists_graph_iso c'
  obtain ⟨e,-⟩ := c.group_equiv_of_graph_iso c' F
  exact ⟨e⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

