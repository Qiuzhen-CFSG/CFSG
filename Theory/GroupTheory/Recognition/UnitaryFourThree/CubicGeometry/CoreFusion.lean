module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.InvolutionFusion
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.Hyperplanes
/-!
# Internal fusion of the source core involutions

Choose a reflection s outside Q in the actual cubic normalizer. Its
internal fusion with z places Q_s in the component stabilizer. In a
source elementary-sixteen plane through s, the two actual core
hyperplanes have order eight and hence a nonidentity intersection a.
Symmetry of core incidence excludes z from Q_s, so za is a noncentral
involution of Q. Pull back by the internal conjugator z to s. The
fixed elementary eight forces the pulled-back z to interchange the
quaternion factors. The same factor-swap calculation puts za into
⟨z,s⟩ up to Q_s-conjugacy, proving internal fusion of z with za.
The existing residual orbit on Q−⟨z⟩ then gives all core involutions.
Source: Aschbacher, Sporadic Groups (1994),45.2–45.6,45.10–45.11, pp.242–249.
-/
public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem core_fixed_eight_swap (h : CentralizerHypothesis z)
    (A : Subgroup G) (hAQ : A≤core z) (hAc : Nat.card A=8)
    (hAp : ∀a∈A,a^2=1) (t : G) (ht : t∈centralizer z) (htQ : t∉core z)
    (hfix : ∀a∈A,t*a=a*t) :
    h.factorData.leftCore.map (MulAut.conj t).toMonoidHom=h.factorData.rightCore := by
  let d := h.factorData
  have hB : Nonempty (d.leftCore≃*QuaternionGroup 2) :=
    ⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hC : Nonempty (d.rightCore≃*QuaternionGroup 2) :=
    ⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hi : Nat.card (d.leftCore⊓d.rightCore:Subgroup G)=2 := by
    rw [d.core_intersection h.involution,Nat.card_zpowers,h.involution]
  have hc : ∀b∈d.leftCore,∀c∈d.rightCore,b*c=c*b := fun b hb c hc=>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) c (pCoreIn_le 2 d.right hc)
  exact (quaternion_factors_swapped_of_fixed_elementary_eight d.leftCore d.rightCore A
    hB hC hi hc (by rw [d.core_span h.involution]; exact h.core_card)
    (by rw [d.core_span h.involution,h.centralizer_core]; exact h.line_le_core)
    (by rwa [d.core_span h.involution]) hAc hAp t
    (by rw [d.core_span h.involution]; exact CentralizerHypothesis.centralizer_normalizes_core ht)
    (by rwa [d.core_span h.involution]) hfix).1

private theorem eights_in_sixteen_intersect (E A B : Subgroup G)
    [IsMulCommutative E] (hE : Nat.card E=16) (hA : Nat.card A=8) (hB : Nat.card B=8)
    (hAE : A≤E) (hBE : B≤E) : ∃a∈A⊓B,a≠1 := by
  have hnorm : B≤normalizer (A:Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro b hb a ha
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a,hAE ha⟩:E) ⟨b,hBE hb⟩)
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B hnorm
  have hsup := card_le_of_le (sup_le hAE hBE)
  rw [hA,hB] at hc
  rw [hE] at hsup
  have hi : A⊓B≠⊥ := by
    intro he
    rw [he,card_bot,one_mul] at hc
    omega
  obtain ⟨a,ha⟩ := ne_bot_iff_exists_ne_one.mp hi
  exact ⟨a,a.property,fun he => ha (Subtype.ext he)⟩

namespace CubicGeometry.SourceConfiguration
variable {h : IsType z} {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)

private theorem core_conjugate_le_component {s g : G}
    (hg : g∈c.componentStabilizer) (hgs : g*z*g⁻¹=s) : core s≤c.componentStabilizer := by
  have hm : (core z).map (MulAut.conj g).toMonoidHom=core s := (map_core (MulAut.conj g) z).trans (congrArg core hgs)
  rw [←hm]
  rintro a ⟨q,hq,rfl⟩
  exact c.componentStabilizer.mul_mem (c.componentStabilizer.mul_mem hg
    (c.core_le_componentStabilizer hq)) (c.componentStabilizer.inv_mem hg)

theorem exists_core_fusion_seed :
    ∃v∈core z, v∉zpowers z ∧ orderOf v=2 ∧
      ∃g∈c.componentStabilizer,g*z*g⁻¹=v := by
  obtain ⟨R⟩ := h.exists_rootPair
  obtain ⟨m,ht,hs,htQ,hsQ⟩ := R.exists_reflected_marking h c.X
    (h.cubic_sylow_image_card P) (map_subtype_le _)
  have htR : m.t∈R.R := (R.involution_mem_R_or_core h m.t ht.1 m.t_order).resolve_right htQ
  have ht2 : m.t^2=1 := m.t_order ▸ pow_orderOf_eq_one m.t
  let : IsElementaryAbelian 2 (zpowers m.t) := IsElementaryAbelian.zpowers_of_pow_eq_one ht2
  obtain ⟨E,htE,hET,hEE,hEc⟩ := R.elementary_in_R_le_plane h (zpowers m.t) (zpowers_le.mpr htR)
  have hE : E≤R.T ∧ IsElementaryAbelian 2 E ∧ Nat.card E=16 := ⟨hET,hEE,hEc⟩
  let : IsElementaryAbelian 2 E := hEE
  have hzE : z∈E := R.E_le_plane h E hE R.z_mem_E
  have hte : m.t∈E := htE (mem_zpowers m.t)
  have htn : m.t∈normalizer (c.V:Set G) := CubicNormalizer.normalizer_normalizes_oddKernel c.X ht.2
  obtain ⟨g,hgn,hgs⟩ := c.kernel_normalizer_involutions_conjugate z m.t
    c.involution_normalizes_kernel htn h.involution m.t_order
  have hg : g∈c.componentStabilizer := c.kernel_normalizer_le_componentStabilizer hgn
  have hzQs : z∉core m.t := fun hh => htQ ((core_incidence_symmetric h z m.t
    (IsConj.refl _) (isConj_iff.mpr ⟨g,hgs⟩)).mp hh)
  have hAc : Nat.card (E⊓core z:Subgroup G)=8 := R.plane_inf_core_card h E hE
  have hBc : Nat.card (E⊓core m.t:Subgroup G)=8 := R.plane_inf_conjugate_core_card h E hE
    m.t hte (by intro he; have hh := m.t_order; simp [he] at hh)
  obtain ⟨a,ha,ha1⟩ := eights_in_sixteen_intersect E (E⊓core z) (E⊓core m.t)
    hEc hAc hBc inf_le_left inf_le_left
  have haE : a∈E := ha.1.1
  have haQ : a∈core z := ha.1.2
  have haQs : a∈core m.t := ha.2.2
  have ha2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian a haE
  have hza : z*a=a*z := congrArg Subtype.val
    (IsMulCommutative.is_comm.comm (⟨z,hzE⟩:E) ⟨a,haE⟩)
  let v := z*a
  have hvE : v∈E := E.mul_mem hzE haE
  have hvQ : v∈core z := (core z).mul_mem (RootPair.z_mem_core h) haQ
  have hvZ : v∉zpowers z := by
    intro hvZ
    have haZ : a∈zpowers z := by
      have hh := (zpowers z).mul_mem (inv_mem (mem_zpowers z)) hvZ
      simpa only [v,inv_mul_cancel_left] using hh
    have hzcard : Nat.card (zpowers z)=2 := by rw [Nat.card_zpowers,h.involution]
    have haz : a=z := by
      obtain ⟨w,hw,he⟩ := (Nat.card_eq_two_iff' (1:zpowers z)).mp hzcard
      exact congrArg Subtype.val ((he ⟨a,haZ⟩ (fun hx=>ha1 (congrArg Subtype.val hx))).trans
        (he ⟨z,mem_zpowers z⟩ (by
          intro hx
          have hz1 : z=1 := congrArg Subtype.val hx
          have hh:=h.involution
          simp only [hz1,orderOf_one] at hh
          omega)).symm)
    exact hzQs (haz ▸ haQs)
  have hv2 : orderOf v=2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian v hvE)
    (fun he=>hvZ (he ▸ (zpowers z).one_mem))
  let e := MulAut.conj g⁻¹
  have het : e m.t=z := by rw [←hgs]; simp [e,mul_assoc]
  have heQ : (core m.t).map e.toMonoidHom=core z := (map_core e m.t).trans (congrArg core het)
  let A := (E⊓core m.t).map e.toMonoidHom
  have hAQ : A≤core z := (map_mono inf_le_right).trans_eq heQ
  have hAcard : Nat.card A=8 := (card_map_of_injective e.injective).trans hBc
  have hAp : ∀x∈A,x^2=1 := by
    rintro x ⟨y,hy,rfl⟩
    rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian y hy.1,map_one]
  let t := e z
  have htC : t∈centralizer z := by
    rw [←het]
    apply mem_centralizer_singleton_iff.mpr
    simpa only [t,map_mul] using congrArg e (mem_centralizer_singleton_iff.mp (R.T_le_centralizer ht.1)).symm
  have htQ' : t∉core z := by
    intro hh
    have hz : z∈core m.t := (mem_core_map_iff e z m.t).mp (het.symm ▸ hh)
    exact hzQs hz
  have hfix : ∀x∈A,t*x=x*t := by
    rintro x ⟨y,hy,rfl⟩
    have hh : z*y=y*z := congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨z,hzE⟩:E) ⟨y,hy.1⟩)
    simpa only [t,map_mul,MulEquiv.coe_toMonoidHom] using congrArg e hh
  let d := h.toCentralizerHypothesis.factorData
  have hswap := core_fixed_eight_swap h.toCentralizerHypothesis A hAQ hAcard hAp t htC htQ' hfix
  have htv : e v*t⁻¹∈d.leftCore⊔d.rightCore := by
    rw [d.core_span h.involution]
    have hea : e a∈core z := hAQ (mem_map_of_mem e.toMonoidHom ⟨haE,haQs⟩)
    have hve : e v*t⁻¹=e a := by
      change e (z*a)*(e z)⁻¹=e a
      rw [hza,map_mul,mul_inv_cancel_right]
    rwa [hve]
  obtain ⟨b,hb,hbcon⟩ := involution_swap_coset_conjugate_intersection d.leftCore d.rightCore
    (fun b hb c hc => d.factors_commute h.involution b (pCoreIn_le 2 d.left hb)
      c (pCoreIn_le 2 d.right hc)) t
    (by change (e z)^2=1; rw [←map_pow,←h.involution,pow_orderOf_eq_one,map_one]) hswap (e v)
    (by rw [←map_pow,←hv2,pow_orderOf_eq_one,map_one]) htv
  have hez : e.symm z=m.t := e.symm_apply_eq.mpr het.symm
  have hbn : e.symm (b⁻¹*e v*b)∈normalizer (c.V:Set G) := by
    have hh := mem_map_of_mem e.symm.toMonoidHom hbcon
    apply (show ((d.leftCore⊓d.rightCore)⊔zpowers t).map e.symm.toMonoidHom ≤ normalizer (c.V:Set G) from ?_) hh
    rw [Subgroup.map_sup,d.core_intersection h.involution,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    change zpowers (e.symm z)⊔zpowers (e.symm (e z)) ≤ _
    rw [hez,e.symm_apply_apply]
    exact sup_le (zpowers_le.mpr htn) (zpowers_le.mpr c.involution_normalizes_kernel)
  have hbQ : b∈core z := (d.core_span h.involution) ▸ (show b∈d.leftCore⊔d.rightCore from mem_sup_left hb)
  have hbQs : e.symm b∈core m.t := by
    rw [←hez,←map_core]
    exact mem_map_of_mem e.symm.toMonoidHom hbQ
  have hbH : e.symm b∈c.componentStabilizer := c.core_conjugate_le_component hg hgs hbQs
  have hbOrder : orderOf (e.symm (b⁻¹*e v*b))=2 := by
    rw [e.symm.orderOf_eq]
    simpa only [MulAut.conj_apply,inv_inv] using
      ((MulAut.conj b⁻¹).orderOf_eq (e v)).trans ((e.orderOf_eq v).trans hv2)
  obtain ⟨k,hk,hke⟩ := c.kernel_normalizer_involution_fused_in_component _ hbn hbOrder
  refine ⟨v,hvQ,hvZ,hv2,(e.symm b)*k,c.componentStabilizer.mul_mem hbH hk,?_⟩
  calc
    _ = e.symm b*(k*z*k⁻¹)*(e.symm b)⁻¹ := by group
    _ = v := by rw [hke,map_mul,map_mul,map_inv,e.symm_apply_apply]; group

theorem core_involution_fused_in_component (v:G) (hv : v∈core z) (hv2 : orderOf v=2) :
    ∃g∈c.componentStabilizer,g*z*g⁻¹=v := by
  by_cases hvZ : v∈zpowers z
  · have hzcard : Nat.card (zpowers z)=2 := by rw [Nat.card_zpowers,h.involution]
    obtain ⟨a,ha,he⟩ := (Nat.card_eq_two_iff' (1:zpowers z)).mp hzcard
    have hz1 : z≠1 := by intro hh; have hi:=h.involution; simp [hh] at hi
    have hv1 : v≠1 := by intro hh; simp [hh] at hv2
    have hvz : z=v := congrArg Subtype.val ((he ⟨z,mem_zpowers z⟩ (fun hh=>hz1 (congrArg Subtype.val hh))).trans
      (he ⟨v,hvZ⟩ (fun hh=>hv1 (congrArg Subtype.val hh))).symm)
    exact ⟨1,c.componentStabilizer.one_mem,by simpa only [one_mul,inv_one,mul_one] using hvz⟩
  · obtain ⟨u,hu,huZ,hu2,g,hg,hgu⟩ := c.exists_core_fusion_seed
    obtain ⟨k,hk,hkv⟩ := h.toCentralizerHypothesis.core_involution_orbit u v hu hv hu2 hv2 huZ hvZ
    have hkH : k∈c.componentStabilizer := c.centralizer_le_componentStabilizer (map_subtype_le _ hk)
    refine ⟨k*g,c.componentStabilizer.mul_mem hkH hg,?_⟩
    calc
      _ = k*(g*z*g⁻¹)*k⁻¹ := by group
      _ = v := by rw [hgu,hkv]

theorem sylow_involution_fused_in_component (R : RootPair z) (v:G)
    (hv : v∈R.T) (hv2 : orderOf v=2) :
    ∃g∈c.componentStabilizer,g*z*g⁻¹=v := by
  by_cases hvQ : v∈core z
  · exact c.core_involution_fused_in_component v hvQ hv2
  · exact c.outside_core_involution_fused_in_component R v hv hv2 hvQ

end CubicGeometry.SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree
