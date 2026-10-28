module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.LocalOrbits
/-!
# The marked equivariant point bijection preserves all adjacency

Reduce the first vertex to W, the neighboring axis I, or an opposite Y
using N(W)-equivariance. The three source adjacency formulas then apply:
normalization of V, membership in V∩D, and K-conjugates of [V,z]. Every
vertex has 36 neighbors, so a bijection preserving edges also reflects
edges. Source: Aschbacher, Sporadic Groups (1994),45.11, pp.248–249.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)
variable {G' : Type*} [Group G'] [Finite G'] {z' : G'} {h' : IsType z'}
variable {P' : Sylow 3 (centralizer z')} (c' : SourceConfiguration h' P')

variable (e:normalizer (c.W:Set G) ≃* normalizer (c'.W:Set G'))
variable (hD:∀n:normalizer (c.W:Set G),n.val∈c.D→(e n).val∈c'.D)
variable (hV:∀n:normalizer (c.W:Set G),n.val∈c.V→(e n).val∈c'.V)
variable (hNV:∀n:normalizer (c.W:Set G),
  n.val∈normalizer (c.V:Set G)→(e n).val∈normalizer (c'.V:Set G'))
variable (hdisp:∀n:normalizer (c.W:Set G),
  (∃k∈c.K,k⁻¹*n.val*k∈⁅c.V,zpowers z⁆)→∃k∈c'.K,k⁻¹*(e n).val*k∈⁅c'.V,zpowers z'⁆)
variable {Y:Subgroup G} {Y':Subgroup G'}
variable (hYL:Y≤c.oppositeFactor) (hY:Nat.card Y=3) (hne:Y≠c.W) (hK:c.K≤normalizer (Y:Set G))
variable (hYL':Y'≤c'.oppositeFactor) (hY':Nat.card Y'=3) (hne':Y'≠c'.W) (hK':c'.K≤normalizer (Y':Set G'))
variable (F:c.points≃c'.points)
variable (hFW:F ⟨c.W,c.point_mem⟩=⟨c'.W,c'.point_mem⟩)
variable (hFI:F ⟨c.otherAxis,c.otherAxis_is_point⟩=⟨c'.otherAxis,c'.otherAxis_is_point⟩)
variable (hFY:F ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩=⟨Y',c'.cubic_in_oppositeFactor_is_point hYL' hY'⟩)
variable (hact:∀(n:normalizer (c.W:Set G))(U:c.points),
  F (c.conjugatePoint U n.val)=c'.conjugatePoint (F U) (e n).val)

include hFI hact in
theorem localMap_base_adj (U:c.points) (hU:c.collinearity.Adj ⟨c.W,c.point_mem⟩ U) :
    c'.collinearity.Adj ⟨c'.W,c'.point_mem⟩ (F U) := by
  obtain ⟨n,hn,he⟩ := c.neighbor_eq_axis_conjugate hU
  have hU' : U=c.conjugatePoint ⟨c.otherAxis,c.otherAxis_is_point⟩ n := Subtype.ext he
  rw [hU',hact ⟨n,hn⟩,hFI]
  have hh := c'.neighbor_conjugate c'.otherAxis_neighbor (e ⟨n,hn⟩).val
  have hw : c'.W.conjBy (e ⟨n,hn⟩).val=c'.W := mem_normalizer_iff_map_conj_eq.mp (e ⟨n,hn⟩).property
  rwa [hw] at hh

include hD hV hNV hYL hY hne hK hYL' hY' hne' hFW hFI hFY hact in
theorem localMap_axis_adj (U:c.points) (hU:c.collinearity.Adj ⟨c.otherAxis,c.otherAxis_is_point⟩ U) :
    c'.collinearity.Adj ⟨c'.otherAxis,c'.otherAxis_is_point⟩ (F U) := by
  rcases (c.reachable_iff_withinTwo U).mp (c.original_point_reachable U) with he|ha|hd
  · rw [he,hFW]
    exact c'.collinearity.adj_symm c'.otherAxis_neighbor
  · obtain ⟨n,hn,he⟩ := c.neighbor_eq_axis_conjugate ha
    have hU' : U=c.conjugatePoint ⟨c.otherAxis,c.otherAxis_is_point⟩ n := Subtype.ext he
    have hneI : c.otherAxis.conjBy n≠c.otherAxis := he ▸ hU.2.1
    have hnv : n∈normalizer (c.V:Set G) :=
      (c.neighboring_axes_adj_iff_normalizes_kernel n hn hneI).mp (he ▸ hU)
    have hneI' : c'.otherAxis.conjBy (e ⟨n,hn⟩).val≠c'.otherAxis := by
      intro hh
      have hh' : F U=F ⟨c.otherAxis,c.otherAxis_is_point⟩ := by
        rw [hU',hact ⟨n,hn⟩,hFI]
        exact Subtype.ext hh
      exact hU.2.1 (congrArg Subtype.val (F.injective hh'))
    rw [hU',hact ⟨n,hn⟩,hFI]
    exact (c'.neighboring_axes_adj_iff_normalizes_kernel _ (e ⟨n,hn⟩).property hneI').mpr (hNV ⟨n,hn⟩ hnv)
  · obtain ⟨d,hdD,he⟩ := c.distance_two_mem_oddPointOrbit hYL hY hne hK hd
    let n : normalizer (c.W:Set G) := ⟨d,c.complement_product.ge (mem_sup_left hdD)⟩
    have hU' : U=c.conjugatePoint ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩ n.val := Subtype.ext he
    have hdV : d∈c.V := ((c.opposite_neighbor_iff_mem_kernel_intersection hYL hY hne d hdD).mp (he ▸ hU)).1
    rw [hU',hact n,hFY]
    exact (c'.opposite_neighbor_iff_mem_kernel_intersection hYL' hY' hne' (e n).val (hD n hdD)).mpr
      ⟨hV n hdV,hD n hdD⟩

include hD hV hNV hYL hY hne hK hYL' hY' hne' hFW hFI hFY hact in
theorem localMap_neighbor_adj (U V:c.points) (hU:c.collinearity.Adj ⟨c.W,c.point_mem⟩ U)
    (hUV:c.collinearity.Adj U V) : c'.collinearity.Adj (F U) (F V) := by
  obtain ⟨n,hn,he⟩ := c.neighbor_eq_axis_conjugate hU
  let nN : normalizer (c.W:Set G) := ⟨n,hn⟩
  have hU' : U=c.conjugatePoint ⟨c.otherAxis,c.otherAxis_is_point⟩ n := Subtype.ext he
  have hback : c.collinearity.Adj ⟨c.otherAxis,c.otherAxis_is_point⟩ (c.conjugatePoint V n⁻¹) := by
    have hh := c.neighbor_conjugate hUV n⁻¹
    change V.val.conjBy n⁻¹∈c.neighbors (U.val.conjBy n⁻¹) at hh
    rwa [he,conjBy_inv] at hh
  have hh := c.localMap_axis_adj c' e hD hV hNV hYL hY hne hK hYL' hY' hne' F hFW hFI hFY hact _ hback
  change c'.collinearity.Adj ⟨c'.otherAxis,c'.otherAxis_is_point⟩ (F (c.conjugatePoint V (nN⁻¹).val)) at hh
  rw [hact (nN⁻¹),map_inv] at hh
  have hh' := c'.neighbor_conjugate hh (e nN).val
  change ((F V).val.conjBy (e nN).val⁻¹).conjBy (e nN).val∈c'.neighbors (c'.otherAxis.conjBy (e nN).val) at hh'
  rw [conjBy_inv'] at hh'
  rw [hU',hact nN,hFI]
  exact hh'


include hD hV hNV hdisp hYL hY hne hK hYL' hY' hne' hK' hFW hFI hFY hact in
theorem localMap_opposite_adj (U:c.points)
    (hU:c.collinearity.Adj ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩ U) :
    c'.collinearity.Adj ⟨Y',c'.cubic_in_oppositeFactor_is_point hYL' hY'⟩ (F U) := by
  rcases (c.reachable_iff_withinTwo U).mp (c.original_point_reachable U) with he|ha|hd
  · have hh : c.collinearity.Adj ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩ ⟨c.W,c.point_mem⟩ := he ▸ hU
    exact (c.opposite_cubic_not_collinear hYL hY hne (c.collinearity.adj_symm hh)).elim
  · have hh := c.localMap_neighbor_adj c' e hD hV hNV hYL hY hne hK hYL' hY' hne'
      F hFW hFI hFY hact U ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩ ha (c.collinearity.adj_symm hU)
    rw [hFY] at hh
    exact c'.collinearity.adj_symm hh
  · obtain ⟨d,hdD,he⟩ := c.distance_two_mem_oddPointOrbit hYL hY hne hK hd
    let n : normalizer (c.W:Set G) := ⟨d,c.complement_product.ge (mem_sup_left hdD)⟩
    have hU' : U=c.conjugatePoint ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩ n.val := Subtype.ext he
    obtain ⟨hd1,hdk⟩ := (c.opposite_adj_iff_displacement_conjugate hYL hY hne hK d hdD).mp (he ▸ hU)
    have hneD : (e n).val≠1 := by
      intro hh
      have hn1 : e n=1 := Subtype.ext hh
      have hn : n=1 := e.injective (hn1.trans e.map_one.symm)
      exact hd1 (congrArg Subtype.val hn)
    rw [hU',hact n,hFY]
    exact (c'.opposite_adj_iff_displacement_conjugate hYL' hY' hne' hK' (e n).val (hD n hdD)).mpr
      ⟨hneD,hdisp n hdk⟩

include hD hV hNV hdisp hYL hY hne hK hYL' hY' hne' hK' hFW hFI hFY hact in
theorem localMap_preserves_adj (U V:c.points) (hUV:c.collinearity.Adj U V) :
    c'.collinearity.Adj (F U) (F V) := by
  obtain ⟨i,n,hn⟩ := c.localRoot_cover hYL hY hne hK U
  let R := c.localRoot Y (c.cubic_in_oppositeFactor_is_point hYL hY) i
  let B := c.conjugatePoint V n.val⁻¹
  have hab : c.collinearity.Adj R B := by
    have hh := c.neighbor_conjugate hUV n.val⁻¹
    have he : U.val=R.val.conjBy n.val := (congrArg Subtype.val hn).symm
    change V.val.conjBy n.val⁻¹∈c.neighbors (U.val.conjBy n.val⁻¹) at hh
    rwa [he,conjBy_inv] at hh
  have hh : c'.collinearity.Adj (F R) (F B) := by
    fin_cases i
    · rw [show R=⟨c.W,c.point_mem⟩ from rfl,hFW]
      exact c.localMap_base_adj c' e F hFI hact B hab
    · rw [show R=⟨c.otherAxis,c.otherAxis_is_point⟩ from rfl,hFI]
      exact c.localMap_axis_adj c' e hD hV hNV hYL hY hne hK hYL' hY' hne'
        F hFW hFI hFY hact B hab
    · rw [show R=⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩ from rfl,hFY]
      exact c.localMap_opposite_adj c' e hD hV hNV hdisp hYL hY hne hK hYL' hY' hne' hK'
        F hFW hFI hFY hact B hab
  have hh' := c'.neighbor_conjugate hh (e n).val
  change c'.collinearity.Adj (c'.conjugatePoint (F R) (e n).val) (c'.conjugatePoint (F B) (e n).val) at hh'
  rw [←hact n,←hact n,hn] at hh'
  have hv : c.conjugatePoint B n.val=V := Subtype.ext (conjBy_inv' V.val n.val)
  rwa [hv] at hh'

include hD hV hNV hdisp hYL hY hne hK hYL' hY' hne' hK' hFW hFI hFY hact in
theorem localMap_adj_iff (U V:c.points) :
    c'.collinearity.Adj (F U) (F V) ↔ c.collinearity.Adj U V := by
  have hforward := c.localMap_preserves_adj c' e hD hV hNV hdisp hYL hY hne hK hYL' hY' hne' hK'
    F hFW hFI hFY hact
  constructor
  · intro hUV
    let f : c.collinearity.neighborSet U→c'.collinearity.neighborSet (F U) :=
      fun V=>⟨F V.val,hforward U V.val V.property⟩
    have hf : Function.Injective f := by
      intro V W he
      exact Subtype.ext (F.injective (congrArg Subtype.val he))
    have hc : Nat.card (c'.collinearity.neighborSet (F U))≤Nat.card (c.collinearity.neighborSet U) := by
      rw [c'.collinearity_neighbor_card,c.collinearity_neighbor_card]
    obtain ⟨W,hW⟩ := (hf.bijective_of_nat_card_le hc).2 ⟨F V,hUV⟩
    have he : W.val=V := F.injective (congrArg Subtype.val hW)
    exact he ▸ W.property
  · exact hforward U V
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
