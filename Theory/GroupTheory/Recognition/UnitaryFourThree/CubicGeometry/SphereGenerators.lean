module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceAction
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
/-!
# Connections inside the original opposite sphere generate D

The selected opposite cubic has 32 neighbors in the opposite sphere.
The corresponding D-conjugators generate a subgroup S normalized by K.
After adjoining W, the derived-group bound makes S W invariant under
N(W). The original quaternion-sixteen action on its quotient by W
forces S W=D. Since W is the Frattini subgroup of extraspecial D,
S=D. This supplies the propagation step for recovering root subgroups
from the graph alone in Asc94,45.11, pp.248–249.
-/
public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)

theorem large_complement_invariant_odd_subgroup (S : Subgroup G)
    (hSD : S≤c.D) (hSK : c.K≤normalizer (S:Set G)) (hS : 27≤Nat.card S) : S=c.D := by
  let A := S⊔c.W
  have hWD : c.W≤c.D := c.odd_fixed.ge.trans inf_le_left
  have hAD : A≤c.D := sup_le hSD hWD
  have hWA : c.W≤A := le_sup_right
  have hDW : c.D≤normalizer (c.W:Set G) := by rw [c.complement_product]; exact le_sup_left
  have hDA : c.D≤normalizer (A:Set G) := le_normalizer_iff_commutator_le_right.mpr
    ((commutator_mono le_rfl hAD).trans (c.odd_derived.trans hWA))
  have hKA : c.K≤normalizer (A:Set G) :=
    (le_inf hSK (c.complement_le.trans inf_le_right)).trans
      (normalizer_inf_normalizer_le_normalizer_sup S c.W)
  have hNA : normalizer (c.W:Set G)≤normalizer (A:Set G) := by
    rw [c.complement_product]
    exact sup_le hDA hKA
  let : (c.W.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer hWA).mpr (hAD.trans hDW)
  obtain ⟨T,hT⟩ := c.quaternion_sylow
  have hzN : z∈normalizer (c.W:Set G) := by
    apply Subgroup.centralizer_le_normalizer _
    intro w hw
    exact mem_centralizer_singleton_iff.mp (c.line_le_fixed hw)
  obtain ⟨Q,hQ,hQN,hzQ⟩ := exists_marked_quaternion_subgroup (normalizer (c.W:Set G)) z hzN h.involution T hT
  have hAc : Nat.card A=243 := (quaternion_inverted_section_order Q A c.W hQ.some z hzQ h.involution
    (hQN.trans hNA) hQN hWA c.line_card (c.odd_card ▸ card_dvd_of_le hAD)
    (hS.trans (card_le_of_le (show S≤A from le_sup_left)))
    (fun a ha => c.odd_inversion a (hAD ha))).1
  have hAD' : A=c.D := eq_of_le_of_card_ge hAD (by rw [hAc,c.odd_card])
  let : IsExtraspecial 3 c.D := c.odd_extraspecial
  have hCW : (center c.D).map c.D.subtype=c.W := by
    apply le_antisymm
    · rintro x ⟨a,ha,rfl⟩
      rw [←c.odd_centralizer]
      intro d hd
      exact congrArg Subtype.val (mem_center_iff.mp ha ⟨d,hd⟩)
    · intro x hx
      refine ⟨⟨x,hWD hx⟩,mem_center_iff.mpr ?_,rfl⟩
      intro d
      exact Subtype.ext ((c.odd_centralizer.symm ▸ hx) d d.property)
  have hfr : (frattini c.D).map c.D.subtype=c.W := by
    rw [IsExtraspecial.frattini_eq_center (p:=3),hCW]
  have hs : S.subgroupOf c.D ⊔ frattini c.D=⊤ := by
    apply map_injective c.D.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hSD,hfr,←MonoidHom.range_eq_map,range_subtype]
    exact hAD'
  have he := frattini_nongenerating hs
  exact le_antisymm hSD (subgroupOf_eq_top.mp he)

def oppositeConnection (Y : Subgroup G) : Subgroup G :=
  closure {d | d∈c.D ∧ Y.conjBy d∈c.neighbors Y}

omit [Finite G] in
theorem oppositeConnection_eq_closure (Y : Subgroup G) :
    c.oppositeConnection Y=closure {d | d∈c.D ∧ Y.conjBy d∈c.neighbors Y} := by rfl

omit [Finite G] in
theorem oppositeConnection_le_odd (Y : Subgroup G) : c.oppositeConnection Y≤c.D :=
  (closure_le _).mpr (fun _ hd=>hd.1)

omit [Finite G] in
theorem oppositeConnection_normalized {Y : Subgroup G} (hK : c.K≤normalizer (Y:Set G)) :
    c.K≤normalizer (c.oppositeConnection Y:Set G) := by
  apply le_normalizer_iff.mpr
  intro k hk x hx
  have hnD : k∈normalizer (c.D:Set G) := CubicLine.normalizer_normalizes_oddKernel c.W (c.complement_le hk).2
  have hkY : Y.conjBy k=Y := mem_normalizer_iff_map_conj_eq.mp (hK hk)
  have hkiY : Y.conjBy k⁻¹=Y := mem_normalizer_iff_map_conj_eq.mp (inv_mem (hK hk))
  have hm : (c.oppositeConnection Y).map (MulAut.conj k).toMonoidHom≤c.oppositeConnection Y := by
    apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    intro d hd
    change k*d*k⁻¹∈c.oppositeConnection Y
    apply Subgroup.subset_closure
    refine ⟨(mem_normalizer_iff.mp hnD d).mp hd.1,?_⟩
    have hh := c.neighbor_conjugate hd.2 k
    rw [hkY] at hh
    have he : Y.conjBy (k*d*k⁻¹)=(Y.conjBy d).conjBy k := by
      rw [conjBy_mul,conjBy_mul,hkiY]
    rwa [he]
  exact hm (mem_map_of_mem (MulAut.conj k).toMonoidHom hx)

theorem opposite_sphere_neighbors_card {Y : c.points}
    (hY : c.collinearity.edist ⟨c.W,c.point_mem⟩ Y=2) :
    (c.collinearity.neighborSet Y \ c.collinearity.neighborSet ⟨c.W,c.point_mem⟩).ncard=32 := by
  have hc := Set.ncard_inter_add_ncard_sdiff_eq_ncard (c.collinearity.neighborSet Y)
    (c.collinearity.neighborSet ⟨c.W,c.point_mem⟩)
  have hi : (c.collinearity.neighborSet Y ∩ c.collinearity.neighborSet ⟨c.W,c.point_mem⟩).ncard=4 := by
    rw [Set.inter_comm]
    exact c.distance_two_common_neighbors_card hY
  have hnc : (c.collinearity.neighborSet Y).ncard=36 := c.collinearity_neighbor_card Y
  rw [hi,hnc] at hc
  omega

theorem oppositeConnection_card_lower {Y : Subgroup G}
    (hYL : Y≤c.oppositeFactor) (hY : Nat.card Y=3) (hne : Y≠c.W)
    (hK : c.K≤normalizer (Y:Set G)) : 32≤Nat.card (c.oppositeConnection Y) := by
  classical
  let Yp : c.points := ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩
  let Wp : c.points := ⟨c.W,c.point_mem⟩
  let F : Set c.points := c.collinearity.neighborSet Yp \ c.collinearity.neighborSet Wp
  have hYdist : c.collinearity.edist Wp Yp=2 := c.opposite_cubic_distance_two hYL hY hne
  have hu (U : F) : ∃d∈c.D,U.val.val=Y.conjBy d := by
    have hneW : U.val≠Wp := by
      intro he
      have hh : c.collinearity.Adj Yp Wp := he ▸ U.property.1
      exact c.opposite_cubic_not_collinear hYL hY hne (c.collinearity.adj_symm hh)
    have hd : c.collinearity.edist Wp U.val=2 := by
      rcases (c.reachable_iff_withinTwo U.val).mp (c.original_point_reachable U.val) with he|ha|hd
      · exact (hneW he).elim
      · exact (U.property.2 ha).elim
      · exact hd
    exact c.distance_two_mem_oddPointOrbit hYL hY hne hK hd
  let f (U : F) : c.oppositeConnection Y := ⟨(hu U).choose,Subgroup.subset_closure
    ⟨(hu U).choose_spec.1,(hu U).choose_spec.2 ▸ U.property.1⟩⟩
  have hf : Function.Injective f := by
    intro U U' he
    have hd : (hu U).choose=(hu U').choose := congrArg Subtype.val he
    apply Subtype.ext
    apply Subtype.ext
    exact (hu U).choose_spec.2.trans ((congrArg (fun d:G=>Y.conjBy d) hd).trans (hu U').choose_spec.2.symm)
  have hh := Nat.card_le_card_of_injective f hf
  change F.ncard≤Nat.card (c.oppositeConnection Y) at hh
  rw [show F.ncard=32 from c.opposite_sphere_neighbors_card hYdist] at hh
  exact hh

theorem oppositeConnection_eq_odd {Y : Subgroup G}
    (hYL : Y≤c.oppositeFactor) (hY : Nat.card Y=3) (hne : Y≠c.W)
    (hK : c.K≤normalizer (Y:Set G)) : c.oppositeConnection Y=c.D :=
  c.large_complement_invariant_odd_subgroup _ (c.oppositeConnection_le_odd Y)
    (c.oppositeConnection_normalized hK)
    ((by decide : 27≤32).trans (c.oppositeConnection_card_lower hYL hY hne hK))
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
