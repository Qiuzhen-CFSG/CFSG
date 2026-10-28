module

public import Theory.GroupTheory.QuaternionCentralProductNineAction

/-!
# Inversion preserves the two independent quaternion factors

A simultaneous inverter of independent cubics cannot swap their quaternion
supports. The restriction to either factor therefore inverts that factor's
cubic action. The fixed core of a single cubic axis is the other factor.
These retain the literal conjugation maps used in Aschbacher(1994),45.8,p245.
-/

public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem QuaternionIndependentCubics.normalizes_factors_of_inversion
    {B C:Subgroup G} (d:QuaternionIndependentCubics B C)
    (hB:Nonempty (B≃*QuaternionGroup 2)) (hC:Nonempty (C≃*QuaternionGroup 2))
    (hi:Nat.card (B⊓C:Subgroup G)=2)
    (hcomm:∀b∈B,∀c∈C,b*c=c*b)
    (r:G) (hr:r∈normalizer (B⊔C:Subgroup G))
    (hinv:∀x∈d.A,r*x*r⁻¹=x⁻¹) :
    r∈normalizer (B:Set G) ∧ r∈normalizer (C:Set G) := by
  let f:=MulAut.conj r
  have hjoin:(B⊔C).map f.toMonoidHom=B⊔C:=mem_normalizer_iff_map_conj_eq.mp hr
  have him (Q:Subgroup G) (he:Nonempty (Q≃*QuaternionGroup 2)) (hQ:Q≤B⊔C) :
      Q.map f.toMonoidHom=B ∨ Q.map f.toMonoidHom=C :=
    quaternion_subgroup_eq_factor B C _ hB hC hi hcomm
      ⟨(Q.equivMapOfInjective f.toMonoidHom f.injective).symm.trans he.some⟩
      ((map_mono hQ).trans_eq hjoin)
  have hCC:C.map f.toMonoidHom=C := by
    rcases him C hC le_sup_right with hCB|hCC
    · have hxC : (d.x:G)⁻¹∈centralizer (B:Set G) := by
        intro b hb
        have hb' : b∈C.map f.toMonoidHom:=hCB.symm ▸ hb
        obtain ⟨q,hq,rfl⟩:=hb'
        rw [←hinv d.x d.x.property]
        change f q*f d.x=f d.x*f q
        rw [←map_mul,←map_mul]
        exact congrArg f (d.x_centralizes q hq)
      have hxB : (d.x:G)∈centralizer (B:Set G) := by
        simpa only [inv_inv] using (centralizer (B:Set G)).inv_mem hxC
      apply False.elim
      apply d.x_actionB_ne_one
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rw [d.actionB_apply]
      change (d.x:G)*(b:G)*(d.x:G)⁻¹=(b:G)
      rw [←hxB b b.property,mul_inv_cancel_right]
    · exact hCC
  have hBB:B.map f.toMonoidHom=B := by
    rcases him B hB le_sup_left with hBB|hBC
    · exact hBB
    · have he:B=C:=map_injective f.injective (hBC.trans hCC.symm)
      have hb8:Nat.card B=8:=by rw [Nat.card_congr hB.some.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
      rw [←he,inf_idem,hb8] at hi
      omega
  exact ⟨mem_normalizer_iff_map_conj_eq.mpr hBB,mem_normalizer_iff_map_conj_eq.mpr hCC⟩

omit [Finite G] in
theorem QuaternionIndependentCubics.inverts_right_action
    {B C:Subgroup G} (d:QuaternionIndependentCubics B C)
    (r:G) (hr:r∈normalizer (C:Set G))
    (hy:r*(d.y:G)*r⁻¹=(d.y:G)⁻¹) :
    C.normalizerMonoidHom ⟨r,hr⟩*d.actionC d.y=
      (d.actionC d.y)⁻¹*C.normalizerMonoidHom ⟨r,hr⟩ := by
  let rn:normalizer (C:Set G):=⟨r,hr⟩
  let yn:normalizer (C:Set G):=⟨d.y,d.normalizes_right d.y.property⟩
  have he:d.actionC d.y=C.normalizerMonoidHom yn := by
    apply MulEquiv.ext
    intro q
    apply Subtype.ext
    exact d.actionC_apply d.y q
  have hh:rn*yn*rn⁻¹=yn⁻¹:=Subtype.ext hy
  have heq:=congrArg C.normalizerMonoidHom hh
  rw [map_mul,map_mul,map_inv,map_inv,←he] at heq
  exact mul_inv_eq_iff_eq_mul.mp heq

theorem QuaternionIndependentCubics.fixed_core_left
    {B C:Subgroup G} (d:QuaternionIndependentCubics B C)
    (hB:Nonempty (B≃*QuaternionGroup 2))
    (hi:Nat.card (B⊓C:Subgroup G)=2) (hc:∀b∈B,∀c∈C,b*c=c*b) :
    (B⊔C)⊓centralizer (zpowers (d.x:G):Set G)=C := by
  have hnorm:C≤normalizer (B:Set G):=(show C≤centralizer (B:Set G) from fun c hc' b hb=>hc b hb c hc').trans (centralizer_le_normalizer _)
  have hCfix:C≤centralizer (zpowers (d.x:G):Set G):=
    le_centralizer_iff.mp (zpowers_le.mpr d.x_centralizes)
  apply le_antisymm
  · intro q hq
    have hp:q∈(↑(B⊔C):Set G):=hq.1
    rw [coe_mul_of_right_le_normalizer_left B C hnorm] at hp
    obtain ⟨b,hb,c,hc',rfl⟩:=hp
    have he:(d.x:G)*(b*c)=(b*c)*(d.x:G):=hq.2 _ (mem_zpowers _)
    have hbfix:b∈centralizer ({(d.x:G)}:Set G):=by
      apply mem_centralizer_singleton_iff.mpr
      apply mul_right_cancel (b:=c)
      calc
        b*(d.x:G)*c=b*(c*(d.x:G)):=by rw [mul_assoc,←d.x_centralizes c hc']
        _ = (d.x:G)*(b*c):=by rw [←mul_assoc,he]
        _ = ((d.x:G)*b)*c:=by group
    have hbC:b∈C:=by
      have hh:b∈(center B).map B.subtype:=d.fixed_left ▸ ⟨hb,hbfix⟩
      rw [←intersection_eq_factor_center B C hB hi hc] at hh
      exact hh.2
    exact C.mul_mem hbC hc'
  · exact le_inf le_sup_right hCfix

end Subgroup
