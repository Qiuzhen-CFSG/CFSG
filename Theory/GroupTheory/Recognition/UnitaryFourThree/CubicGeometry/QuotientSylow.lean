module

public import Theory.GroupTheory.QuotientTrivialIntersection
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.TrivialIntersection
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.Action

/-!
# The actual elementary-nine TI Sylow quotient

The literal faithful normalizer quotient N(V)/C(V)=N(V)/V carries the original
Sylow product to an elementary subgroup of order9. Its distinct conjugates
are disjoint, by the preceding source intersection theorem. The actual
Sylow-normalizer preimage is N(Q), whose source index over V is36.
No quotient action, Sylow model or TI property is assumed.
Source: Aschbacher, Sporadic Groups (1994),45.9,printed pp246–247.
-/

public section
open Subgroup
open scoped Pointwise

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G:Type*} [Group G] [Finite G] {z:G} {h:IsType z} {P:Sylow 3 (centralizer z)}
variable (c:SourceConfiguration h P)

theorem internal_sylow_intersections :
    let V:=c.toSourceData.V
    let M:=normalizer (V:Set G)
    let Q:=c.toSourceData.Q.subgroupOf M
    ∀g:M,g∉normalizer (Q:Set M)→Q⊓Q.map (MulAut.conj g).toMonoidHom=V.subgroupOf M := by
  dsimp only
  let V:=c.toSourceData.V
  let M:=normalizer (V:Set G)
  let Q:=c.toSourceData.Q
  have hQM:Q≤M:=(h.cubic_kernel_outside_fixed_planes P c.actors c.actors_eq
    c.odd_split c.odd_card c.odd_extraspecial).1
  intro g hg
  have hgQ:(g:G)∉normalizer (Q:Set G):=by
    intro hgQ
    apply hg
    rw [←subgroupOf_normalizer_eq hQM]
    exact hgQ
  have ht:=c.sylow_intersection_eq_kernel g g.property hgQ
  ext x
  change (x:M)∈Q.subgroupOf M⊓(Q.subgroupOf M).map (MulAut.conj g).toMonoidHom ↔ (x:G)∈V
  rw [mem_inf,mem_map_equiv]
  change ((x:G)∈Q ∧ (MulAut.conj (g:G)).symm (x:G)∈Q) ↔ (x:G)∈V
  rw [←mem_map_equiv,←mem_inf,ht]

theorem quotient_sylow_ti :
    let V:=c.toSourceData.V
    let M:=normalizer (V:Set G)
    let f:=NormalizerAction.quotient V
    let Q:=(c.toSourceData.Q.subgroupOf M).map f
    ∀g:NormalizerAction.Star V,g∉normalizer (Q:Set (NormalizerAction.Star V))→
      Disjoint Q (Q.map (MulAut.conj g).toMonoidHom) := by
  let V:=c.toSourceData.V
  let M:=normalizer (V:Set G)
  let f:=NormalizerAction.quotient V
  have hk:f.ker=V.subgroupOf M:=by
    change (QuotientGroup.mk' (NormalizerAction.C V)).ker=V.subgroupOf M
    rw [QuotientGroup.ker_mk']
    change (Subgroup.centralizer (V:Set G)).subgroupOf M=V.subgroupOf M
    rw [h.cubic_kernel_centralizer P]
  apply ti_image_of_kernel_intersections f (QuotientGroup.mk'_surjective _) (c.toSourceData.Q.subgroupOf M)
    (by rw [hk];exact subgroupOf_mono M le_sup_left)
  simpa only [hk] using c.internal_sylow_intersections
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G:Type*} [Group G] [Finite G] {z:G} {h:IsType z} {P:Sylow 3 (centralizer z)}
variable (c:SourceConfiguration h P)

theorem quotient_kernel_eq :
    (NormalizerAction.quotient c.toSourceData.V).ker=
      c.toSourceData.V.subgroupOf (normalizer (c.toSourceData.V:Set G)) := by
  change (QuotientGroup.mk' (NormalizerAction.C c.toSourceData.V)).ker=_
  rw [QuotientGroup.ker_mk']
  change (Subgroup.centralizer (c.toSourceData.V:Set G)).subgroupOf _=_
  rw [h.cubic_kernel_centralizer P]

@[expose] noncomputable def quotientSylow : Sylow 3 (NormalizerAction.Star c.toSourceData.V) :=
  (c.sylow.subtype (by
    rw [c.sylow_eq]
    exact (h.cubic_kernel_outside_fixed_planes P c.actors c.actors_eq
      c.odd_split c.odd_card c.odd_extraspecial).1)).mapSurjective (QuotientGroup.mk'_surjective _)

theorem quotientSylow_coe :
    (c.quotientSylow:Subgroup (NormalizerAction.Star c.toSourceData.V))=
      (c.toSourceData.Q.subgroupOf (normalizer (c.toSourceData.V:Set G))).map
        (NormalizerAction.quotient c.toSourceData.V) := by
  change ((c.sylow:Subgroup G).subgroupOf _).map _=_
  rw [c.sylow_eq]
  rfl

theorem quotientSylow_card : Nat.card c.quotientSylow=9 := by
  let V:=c.toSourceData.V
  let M:=normalizer (V:Set G)
  let f:=NormalizerAction.quotient V
  let Q:=c.toSourceData.Q.subgroupOf M
  have hQM:c.toSourceData.Q≤M:=(h.cubic_kernel_outside_fixed_planes P c.actors c.actors_eq
    c.odd_split c.odd_card c.odd_extraspecial).1
  have hk:f.ker=V.subgroupOf M:=c.quotient_kernel_eq
  have hKQ:f.ker≤Q:=by rw [hk];exact subgroupOf_mono M le_sup_left
  have hQc:Nat.card Q=729:=(Nat.card_congr (subgroupOfEquivOfLe hQM).toEquiv).trans c.sylow_card
  have hKc:Nat.card f.ker=81:=by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe V.le_normalizer).toEquiv]
    exact c.kernel_card
  have hh:=relIndex_mul_relIndex (⊥:Subgroup M) f.ker Q bot_le hKQ
  rw [relIndex_bot_left,relIndex_bot_left,hKc,hQc,relIndex_ker] at hh
  change Nat.card (c.quotientSylow:Subgroup (NormalizerAction.Star V))=9
  rw [c.quotientSylow_coe]
  change Nat.card (Q.map f)=9
  omega

theorem quotientSylow_Ti (g:NormalizerAction.Star c.toSourceData.V)
    (hg:g∉normalizer (c.quotientSylow:Set (NormalizerAction.Star c.toSourceData.V))) :
    Disjoint (c.quotientSylow:Subgroup (NormalizerAction.Star c.toSourceData.V))
      ((c.quotientSylow:Subgroup (NormalizerAction.Star c.toSourceData.V)).map (MulAut.conj g).toMonoidHom) := by
  have hh:=c.quotient_sylow_ti g
  rw [←c.quotientSylow_coe] at hh
  exact hh hg
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G:Type*} [Group G] [Finite G] {z:G} {h:IsType z} {P:Sylow 3 (centralizer z)}
variable (c:SourceConfiguration h P)

theorem quotientSylow_elementary : IsElementaryAbelian 3 c.quotientSylow := by
  let V:=c.toSourceData.V
  let D:=c.toSourceData.D
  let M:=normalizer (V:Set G)
  let f:=NormalizerAction.quotient V
  have hQM:c.toSourceData.Q≤M:=(h.cubic_kernel_outside_fixed_planes P c.actors c.actors_eq
    c.odd_split c.odd_card c.odd_extraspecial).1
  have hDM:D≤M:=le_sup_right.trans hQM
  let :IsMulCommutative c.quotientSylow:=IsPGroup.isMulCommutative_of_card_eq_prime_sq (p:=3) c.quotientSylow_card
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  apply Subtype.ext
  have hx: (x:NormalizerAction.Star V)∈(c.toSourceData.Q.subgroupOf M).map f:=
    c.quotientSylow_coe.le x.property
  obtain ⟨q,hq,hqx⟩:=hx
  have hh:(q:G)∈(V:Set G)*(D:Set G):=by
    rw [←coe_mul_of_right_le_normalizer_left V D hDM]
    exact hq
  obtain ⟨v,hv,d,hd,he⟩:=hh
  let vn:M:=⟨v,V.le_normalizer hv⟩
  let dn:M:=⟨d,hDM hd⟩
  have hqeq:q=vn*dn:=Subtype.ext he.symm
  have hfv:f vn=1:=c.quotient_kernel_eq.ge hv
  have hx': (x:NormalizerAction.Star V)=f dn:=by
    rw [←hqx,hqeq,map_mul,hfv,one_mul]
  change (x:NormalizerAction.Star V)^3=1
  rw [hx',←map_pow,show dn^3=1 from Subtype.ext (c.odd_cube d hd),map_one]
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G:Type*} [Group G] [Finite G] {z:G} {h:IsType z} {P:Sylow 3 (centralizer z)}
variable (c:SourceConfiguration h P)

theorem quotientSylow_normalizer_preimage :
    (normalizer (c.quotientSylow:Set (NormalizerAction.Star c.toSourceData.V))).comap
      (NormalizerAction.quotient c.toSourceData.V)=
      (normalizer (c.toSourceData.Q:Set G)).subgroupOf (normalizer (c.toSourceData.V:Set G)) := by
  let V:=c.toSourceData.V
  let M:=normalizer (V:Set G)
  let f:=NormalizerAction.quotient V
  have hQM:c.toSourceData.Q≤M:=(h.cubic_kernel_outside_fixed_planes P c.actors c.actors_eq
    c.odd_split c.odd_card c.odd_extraspecial).1
  have hk:f.ker≤c.toSourceData.Q.subgroupOf M:=by
    rw [c.quotient_kernel_eq]
    exact subgroupOf_mono M le_sup_left
  change (normalizer ((c.quotientSylow:Subgroup (NormalizerAction.Star V)):Set _)).comap f=_
  have hf:Function.Surjective f:=QuotientGroup.mk'_surjective _
  rw [comap_normalizer_eq_of_surjective _ hf,
    c.quotientSylow_coe,comap_map_eq_self hk,←subgroupOf_normalizer_eq hQM]

theorem quotientSylow_normalizer_card :
    Nat.card (normalizer (c.quotientSylow:Set (NormalizerAction.Star c.toSourceData.V)))=36 := by
  let V:=c.toSourceData.V
  let M:=normalizer (V:Set G)
  let f:=NormalizerAction.quotient V
  let N:=normalizer (c.toSourceData.Q:Set G)
  let B:=normalizer (c.quotientSylow:Set (NormalizerAction.Star V))
  have hNM:N≤M:=by
    have hh:=c.common_normalizer.le.trans inf_le_left
    change normalizer ((c.sylow:Subgroup G):Set G)≤M at hh
    rwa [c.sylow_eq] at hh
  have hi:V.relIndex N=36:=by
    have hh:=c.normalizer_index
    change V.relIndex (normalizer ((c.sylow:Subgroup G):Set G))=36 at hh
    rwa [c.sylow_eq] at hh
  have hi':(V.subgroupOf M).relIndex (N.subgroupOf M)=36:=by
    have hh:=relIndex_map_map_of_injective (f:=M.subtype) (V.subgroupOf M) (N.subgroupOf M) M.subtype_injective
    rw [map_subgroupOf_eq_of_le V.le_normalizer,map_subgroupOf_eq_of_le hNM] at hh
    exact hh.symm.trans hi
  have hh:=(B.comap f).relIndex_ker f
  have hf:Function.Surjective f:=QuotientGroup.mk'_surjective _
  rw [map_comap_eq_self (fun x _=>hf x)] at hh
  rw [c.quotient_kernel_eq,c.quotientSylow_normalizer_preimage] at hh
  exact hh.symm.trans hi'
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
