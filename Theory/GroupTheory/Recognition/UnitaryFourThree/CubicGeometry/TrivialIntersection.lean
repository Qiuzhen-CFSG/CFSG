module

public import Theory.GroupTheory.TernaryPlaneActionObstruction
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.FixedPlaneAction

/-!
# Trivial intersection modulo the original elementary kernel

Suppose two source Sylow products meet outside V. Their common element fixes
an order9 plane L in V, contained in both conjugate extraspecial factors.
The two central cubic lines are distinct and are precisely the fixed groups
of their induced actions on L. Those actions, together with the original
involution, generate GL₂(3); this would force16 to divide |N_G(V)|, contrary
to its proved Sylow-two order8. Hence the intersection is exactly V.

The final theorem constructs all chosen data from IsType. No TI, action
model, or recognition certificate is assumed.
Source: Aschbacher, Sporadic Groups (1994),45.9,printed p246.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G:Type*} [Group G] [Finite G] {z:G} {h:IsType z} {P:Sylow 3 (centralizer z)}
variable (c:SourceConfiguration h P)

theorem sylow_intersection_le_kernel (g:G)
    (hg:g∈normalizer (c.toSourceData.V:Set G))
    (hgQ:g∉normalizer (c.toSourceData.Q:Set G)) :
    c.toSourceData.Q⊓c.toSourceData.Q.map (MulAut.conj g).toMonoidHom≤c.toSourceData.V := by
  let V:=c.toSourceData.V
  let D:=c.toSourceData.D
  let W:=c.toSourceData.W
  let Q:=c.toSourceData.Q
  let M:=normalizer (V:Set G)
  let e:=MulAut.conj g
  let D':=D.map e.toMonoidHom
  let W':=W.map e.toMonoidHom
  have hVe:V.map e.toMonoidHom=V:=mem_normalizer_iff_map_conj_eq.mp hg
  have hQNM:Q≤M:=(h.cubic_kernel_outside_fixed_planes P c.actors c.actors_eq
    c.odd_split c.odd_card c.odd_extraspecial).1
  have hDM:D≤M:=le_sup_right.trans hQNM
  have hD'M:D'≤M:=by
    have hh:=map_mono hDM (f:=e.toMonoidHom)
    rw [map_normalizer_eq_of_bijective V e.bijective,hVe] at hh
    exact hh
  have hWne:W≠W':=by
    intro he
    have hgW:g∈normalizer (W:Set G):=mem_normalizer_iff_map_conj_eq.mpr he.symm
    apply hgQ
    have hh:g∈normalizer (c.sylow:Set G):=c.common_normalizer.ge ⟨hg,hgW⟩
    change g∈normalizer ((c.sylow:Subgroup G):Set G) at hh
    rwa [c.sylow_eq] at hh
  rintro x ⟨hx,hxg⟩
  by_contra hxV
  let L:=V⊓Subgroup.centralizer ({x}:Set G)
  obtain ⟨hL,hQN,hWL,hLD⟩:=c.outside_fixed_data x hx hxV
  obtain ⟨y,hy,hey⟩:=hxg
  change e y=x at hey
  have hyV:y∉V:=by
    intro hyV
    apply hxV
    rw [←hey]
    exact hVe.le (mem_map_of_mem e.toMonoidHom hyV)
  obtain ⟨hLy,hQNy,hWy,hLyD⟩:=c.outside_fixed_data y hy hyV
  have hLyMap:(V⊓Subgroup.centralizer ({y}:Set G)).map e.toMonoidHom=L:=by
    rw [map_inf _ _ _ e.injective,hVe,Theory.GroupTheory.map_centralizer_equiv,
      Set.image_singleton,hey]
  have hQ'NL:Q.map e.toMonoidHom≤normalizer (L:Set G):=by
    have hh:=map_mono hQNy (f:=e.toMonoidHom)
    rw [map_normalizer_eq_of_bijective _ e.bijective,hLyMap] at hh
    exact hh
  have hLD':L≤D':=by
    rw [←hLyMap]
    exact map_mono hLyD
  have hW'L:W'≤L:=by
    rw [←hLyMap]
    exact map_mono hWy
  have hCD':Subgroup.centralizer (D':Set G)=W':=by
    have hh:=Theory.GroupTheory.map_centralizer_equiv (D:Set G) e
    rw [c.odd_centralizer] at hh
    exact hh.symm
  have hfD:L⊓Subgroup.centralizer (D:Set G)=W:=by
    rw [c.odd_centralizer,inf_eq_right.mpr hWL]
  have hfD':L⊓Subgroup.centralizer (D':Set G)=W':=by
    rw [hCD',inf_eq_right.mpr hW'L]
  have hWp:Nat.card W'=3:=(card_map_of_injective e.injective).trans c.line_card
  have hfDn:L⊓Subgroup.centralizer (D:Set G)≠L:=by
    rw [hfD]
    intro he
    have hh:=Nat.card_congr (MulEquiv.subgroupCongr he).toEquiv
    rw [c.line_card,hL] at hh
    omega
  have hfD'n:L⊓Subgroup.centralizer (D':Set G)≠L:=by
    rw [hfD']
    intro he
    have hh:=Nat.card_congr (MulEquiv.subgroupCongr he).toEquiv
    rw [hWp,hL] at hh
    omega
  have hfne:L⊓Subgroup.centralizer (D:Set G)≠L⊓Subgroup.centralizer (D':Set G):=by
    rw [hfD,hfD']
    exact hWne
  let :IsElementaryAbelian 3 V:=c.kernel_elementary
  let :IsElementaryAbelian 3 L:=IsElementaryAbelian.of_injective
    (inclusion (show L≤V from inf_le_left)) (inclusion_injective _)
  have hDp:IsPGroup 3 D:=IsPGroup.of_card (n:=5) c.odd_card
  have hz2:z^2=1:=by rw [←h.involution];exact pow_orderOf_eq_one z
  have h16:16∣Nat.card M:=ternary_plane_normalizer_sixteen M L D D' hL hDp (hDp.map e.toMonoidHom)
    hDM hD'M (le_sup_right.trans hQN) ((map_mono le_sup_right).trans hQ'NL)
    hfDn hfD'n hfne z c.involution_normalizes_kernel (c.outside_fixed_involution x hx hxV) hz2
    (c.outside_fixed_action_inversion x hx hxV)
  exact h.cubic_kernel_normalizer_not_sixteen P h16
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G:Type*} [Group G] [Finite G] {z:G} {h:IsType z} {P:Sylow 3 (centralizer z)}

theorem sylow_intersection_eq_kernel (c:SourceConfiguration h P) (g:G)
    (hg:g∈normalizer (c.toSourceData.V:Set G))
    (hgQ:g∉normalizer (c.toSourceData.Q:Set G)) :
    c.toSourceData.Q⊓c.toSourceData.Q.map (MulAut.conj g).toMonoidHom=c.toSourceData.V := by
  apply le_antisymm (c.sylow_intersection_le_kernel g hg hgQ)
  refine le_inf le_sup_left ?_
  have he:=mem_normalizer_iff_map_conj_eq.mp hg
  exact he.ge.trans (map_mono le_sup_left)
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem original_cubic_sylow_intersections (h:IsType z) (P:Sylow 3 (centralizer z)) :
    ∃c:CubicGeometry.SourceConfiguration h P,∀g:G,
      g∈normalizer (c.toSourceData.V:Set G)→g∉normalizer (c.toSourceData.Q:Set G)→
      c.toSourceData.Q⊓c.toSourceData.Q.map (MulAut.conj g).toMonoidHom=c.toSourceData.V := by
  obtain ⟨c⟩:=h.original_cubic_source_configuration P
  exact ⟨c,c.sylow_intersection_eq_kernel⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
