module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.ReflectedMarking.Dihedral
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.ReflectedMarking.Sylow
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.Elementary
public import Theory.GroupAction.NineReflectionProduct
public import Theory.GroupAction.KleinFourFactorization.Ambient
public import Theory.GroupTheory.QuaternionCentralProductNineAction.NonInversion
/-!
# The actual ternary-plane action of the two source reflections

Every original Sylow involution outside Q lies in a root plane and hence
interchanges the actual quaternion cores. Independent cubic axes show that
such interchange is not inversion on X. Its action is nontrivial because
the kernel on Tx is the marked line. The exact fixed subgroup therefore
has order three. Brauer–Wielandt then proves that the product of the two
reflections inverts X. All actions are the original normalizer maps.

Source: Aschbacher, Sporadic Groups,45.3(5) and45.7, pp.243–245.
-/
@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G:Type*} [Group G] [Finite G] {z:G}
namespace RootPair
variable (P:RootPair z)

theorem cubicSylow_centralizer_intersection (h:IsType z) (X:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z) :
    P.cubicSylow X⊓Subgroup.centralizer (X:Set G)=zpowers z := by
  let N:=centralizer z⊓normalizer (X:Set G)
  have hUN:P.cubicSylow X≤N := le_inf (inf_le_left.trans P.T_le_centralizer) inf_le_right
  let S:Sylow 2 N := Sylow.ofCard ((P.cubicSylow X).subgroupOf N) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv,P.cubicSylow_card h X hX hXH,
      h.cubic_local_normalizer_card X hX hXH]
    decide +kernel)
  have he:(S:Subgroup N).map N.subtype=P.cubicSylow X := map_subgroupOf_eq_of_le hUN
  have hh:=h.local_cubic_sylow_centralizer_intersection X hX hXH S
  rwa [he] at hh

theorem T_involution_swaps_core_factors (h:IsType z) (t:G)
    (ht:t∈P.T) (ht2:t^2=1) (htQ:t∉core z) :
    h.toCentralizerHypothesis.factorData.leftCore.map (MulAut.conj t).toMonoidHom=
      h.toCentralizerHypothesis.factorData.rightCore ∧
    h.toCentralizerHypothesis.factorData.rightCore.map (MulAut.conj t).toMonoidHom=
      h.toCentralizerHypothesis.factorData.leftCore := by
  have htne:t≠1 := fun he=>htQ (he ▸ (core z).one_mem)
  have htR:t∈P.R := (P.involution_mem_R_or_core h t ht (orderOf_eq_prime ht2 htne)).resolve_right htQ
  let : IsElementaryAbelian 2 (zpowers t) := IsElementaryAbelian.zpowers_of_pow_eq_one ht2
  obtain ⟨V,hUV,hVT,hVE,hVc⟩:=P.elementary_in_R_le_plane h (zpowers t) (zpowers_le.mpr htR)
  have htv:t∈V := hUV (mem_zpowers t)
  let d:=h.toCentralizerHypothesis.factorData
  have hB:Nonempty (d.leftCore≃*QuaternionGroup 2) := ⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hC:Nonempty (d.rightCore≃*QuaternionGroup 2) := ⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hi:Nat.card (d.leftCore⊓d.rightCore:Subgroup G)=2 := by
    rw [d.core_intersection h.involution,Nat.card_zpowers,h.involution]
  have hc:∀b∈d.leftCore,∀c∈d.rightCore,b*c=c*b := fun b hb c hc=>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) c (pCoreIn_le 2 d.right hc)
  let := hVE
  exact quaternion_factors_swapped_of_fixed_elementary_eight d.leftCore d.rightCore
    (V⊓core z) hB hC hi hc (by rw [d.core_span h.involution]; exact h.toCentralizerHypothesis.core_card)
    (by rw [d.core_span h.involution,h.toCentralizerHypothesis.centralizer_core]; exact h.toCentralizerHypothesis.line_le_core)
    (by rw [d.core_span h.involution]; exact inf_le_right)
    (P.plane_inf_core_card h V ⟨hVT,hVE,hVc⟩) (fun u hu=>elemPow_eq_one_of_isElementaryAbelian u hu.1) t
    (by rw [d.core_span h.involution]; exact CentralizerHypothesis.centralizer_normalizes_core (P.T_le_centralizer ht))
    (by rwa [d.core_span h.involution])
    (fun u hu=>congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨t,htv⟩:V) ⟨u,hu.1⟩))

theorem cubic_involution_not_inverting (h:IsType z) (X:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z) (t:G)
    (ht:t∈P.T) (ht2:t^2=1) (htQ:t∉core z) :
    ¬∀x∈X,t*x*t⁻¹=x⁻¹ := by
  let d:=h.toCentralizerHypothesis.factorData
  have hB:Nonempty (d.leftCore≃*QuaternionGroup 2) := ⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hC:Nonempty (d.rightCore≃*QuaternionGroup 2) := ⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hi:Nat.card (d.leftCore⊓d.rightCore:Subgroup G)=2 := by
    rw [d.core_intersection h.involution,Nat.card_zpowers,h.involution]
  have hc:∀b∈d.leftCore,∀c∈d.rightCore,b*c=c*b := fun b hb c hc=>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) c (pCoreIn_le 2 d.right hc)
  have hself:Subgroup.centralizer (d.leftCore⊔d.rightCore:Subgroup G)≤d.leftCore⊔d.rightCore := by
    rw [d.core_span h.involution,h.toCentralizerHypothesis.centralizer_core]
    exact h.toCentralizerHypothesis.line_le_core
  have hnormal:centralizer z≤normalizer (d.leftCore⊔d.rightCore:Subgroup G) := by
    rw [d.core_span h.involution]
    exact CentralizerHypothesis.centralizer_normalizes_core
  obtain ⟨actors,ha⟩:=independent_cubics_of_nine_subgroup d.leftCore d.rightCore X hB hC hi hc hself hX (hXH.trans hnormal)
  have hs:=P.T_involution_swaps_core_factors h t ht ht2 htQ
  intro hinv
  let x:G:=actors.x
  have hxX:x∈X := ha ▸ actors.x.property
  have hy:t*x*t⁻¹∈Subgroup.centralizer (d.leftCore:Set G) := by
    rw [←hs.2]
    rintro _ ⟨c,hc',rfl⟩
    change (t*c*t⁻¹)*(t*x*t⁻¹)=(t*x*t⁻¹)*(t*c*t⁻¹)
    have he:c*x=x*c := actors.x_centralizes c hc'
    calc
      _ = t*(c*x)*t⁻¹ := by group
      _ = t*(x*c)*t⁻¹ := by rw [he]
      _ = _ := by group
  rw [hinv x hxX] at hy
  have hx:x∈Subgroup.centralizer (d.leftCore:Set G) := by simpa only [inv_inv] using (Subgroup.centralizer (d.leftCore:Set G)).inv_mem hy
  apply actors.x_actionB_ne_one
  ext b
  rw [actors.actionB_apply]
  change x*(b:G)*x⁻¹=b
  rw [←hx b b.property,mul_inv_cancel_right]

theorem cubicSylow_action_eq_one_iff (h:IsType z) (X:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z) (t:G) (ht:t∈P.cubicSylow X) :
    X.normalizerMonoidHom ⟨t,ht.2⟩=1 ↔ t∈zpowers z := by
  have he:X.normalizerMonoidHom ⟨t,ht.2⟩=1 ↔ t∈Subgroup.centralizer (X:Set G) := by
    constructor
    · intro he x hx
      have hh:=congrArg Subtype.val (DFunLike.congr_fun he (⟨x,hx⟩:X))
      change t*x*t⁻¹=x at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hc
      ext x
      change t*(x:G)*t⁻¹=x
      rw [←hc x x.property,mul_inv_cancel_right]
  rw [he]
  constructor
  · intro hc
    exact (P.cubicSylow_centralizer_intersection h X hX hXH) ▸ ⟨ht,hc⟩
  · intro hz
    have hc:t∈P.cubicSylow X⊓Subgroup.centralizer (X:Set G) :=
      (P.cubicSylow_centralizer_intersection h X hX hXH).symm ▸ hz
    exact hc.2

theorem cubic_involution_fixed_card (h:IsType z) (X:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z) (t:G)
    (ht:t∈P.cubicSylow X) (ht2:t^2=1) (htQ:t∉core z) :
    Nat.card (X⊓Subgroup.centralizer ({t}:Set G):Subgroup G)=3 := by
  let a:MulAut X:=X.normalizerMonoidHom ⟨t,ht.2⟩
  let : IsElementaryAbelian 3 X := h.toCentralizerHypothesis.nine_elementary X hX hXH
  have ha:a^2=1 := by
    change (X.normalizerMonoidHom ⟨t,ht.2⟩)^2=1
    rw [←map_pow]
    have he:(⟨t,ht.2⟩:normalizer (X:Set G))^2=1 := Subtype.ext ht2
    rw [he,map_one]
  have hane:a≠1 := fun he=>htQ (h.toCentralizerHypothesis.line_le_core
    ((P.cubicSylow_action_eq_one_iff h X hX hXH t ht).mp he))
  have han:¬∀x:X,a x=x⁻¹ := by
    intro hi
    apply P.cubic_involution_not_inverting h X hX hXH t ht.1 ht2 htQ
    intro x hx
    exact congrArg Subtype.val (hi ⟨x,hx⟩)
  have hf:=MulAut.fixed_card_three_of_nonscalar_involution hX a ha hane han
  exact (Nat.card_congr (X.normalizerFixedEquiv ⟨t,ht.2⟩).toEquiv).symm.trans hf

theorem cubic_reflection_rotation_inverts (h:IsType z) (X:Subgroup G)
    (hX:Nat.card X=9) (hXH:X≤centralizer z) (t s:G)
    (ht:t∈P.cubicSylow X) (hs:s∈P.cubicSylow X)
    (ht2:t^2=1) (hs2:s^2=1) (htQ:t∉core z) (hsQ:s∉core z)
    (hst:s*t*s⁻¹=t*z) : ∀x∈X,(s*t)*x*(s*t)⁻¹=x⁻¹ := by
  let sn:normalizer (X:Set G):=⟨s,hs.2⟩
  let tn:normalizer (X:Set G):=⟨t,ht.2⟩
  have hzN:z∈normalizer (X:Set G) := (centralizer_le_normalizer _) (fun x hx=>
    mem_centralizer_singleton_iff.mp (hXH hx))
  let zn:normalizer (X:Set G):=⟨z,hzN⟩
  let a:=X.normalizerMonoidHom sn
  let b:=X.normalizerMonoidHom tn
  have hza:X.normalizerMonoidHom zn=1 := by
    ext x
    change z*(x:G)*z⁻¹=x
    rw [←mem_centralizer_singleton_iff.mp (hXH x.property),mul_inv_cancel_right]
  have hab:a*b*a⁻¹=b := by
    have hh:sn*tn*sn⁻¹=tn*zn := Subtype.ext hst
    have hm:=congrArg X.normalizerMonoidHom hh
    simpa only [map_mul,map_inv,hza,mul_one] using hm
  have hc:Commute a b := by
    change a*b=b*a
    exact mul_inv_eq_iff_eq_mul.mp hab
  have ha:Function.Involutive a := by
    have hh:sn^2=1 := Subtype.ext hs2
    have he:a^2=1 := by change (X.normalizerMonoidHom sn)^2=1; rw [←map_pow,hh,map_one]
    intro x
    exact DFunLike.congr_fun he x
  have hb:Function.Involutive b := by
    have hh:tn^2=1 := Subtype.ext ht2
    have he:b^2=1 := by change (X.normalizerMonoidHom tn)^2=1; rw [←map_pow,hh,map_one]
    intro x
    exact DFunLike.congr_fun he x
  have hsi:s⁻¹=s := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs2)
  have htz:t*z=z*t := mem_centralizer_singleton_iff.mp (P.T_le_centralizer ht.1)
  have hst2:(s*t)^2=z := by
    calc
      (s*t)^2 = (s*t*s⁻¹)*t := by rw [hsi]; simp only [pow_two]; group
      _ = (t*z)*t := by rw [hst]
      _ = z := by rw [htz,mul_assoc,←pow_two,ht2,mul_one]
  have hne:a*b≠1 := by
    intro he
    have hm:X.normalizerMonoidHom ⟨s*t,(normalizer (X:Set G)).mul_mem hs.2 ht.2⟩=1 := by
      change X.normalizerMonoidHom (sn*tn)=1
      rwa [map_mul]
    have hstZ:s*t∈zpowers z := (P.cubicSylow_action_eq_one_iff h X hX hXH (s*t)
      ((P.cubicSylow X).mul_mem hs ht)).mp hm
    have hz2:z^2=1 := h.involution ▸ pow_orderOf_eq_one z
    let : IsElementaryAbelian 2 (zpowers z) := IsElementaryAbelian.zpowers_of_pow_eq_one hz2
    have he:(s*t)^2=1 := elemPow_eq_one_of_isElementaryAbelian (s*t) hstZ
    have hz1:z=1 := hst2.symm.trans he
    have hh:=h.involution
    simp [hz1] at hh
  let : IsElementaryAbelian 3 X := h.toCentralizerHypothesis.nine_elementary X hX hXH
  have haf:Nat.card a.fixedSubgroup=3 := (Nat.card_congr (X.normalizerFixedEquiv sn).toEquiv).trans
    (P.cubic_involution_fixed_card h X hX hXH s hs hs2 hsQ)
  have hbf:Nat.card b.fixedSubgroup=3 := (Nat.card_congr (X.normalizerFixedEquiv tn).toEquiv).trans
    (P.cubic_involution_fixed_card h X hX hXH t ht ht2 htQ)
  have hi:=MulAut.reflection_product_inverts_of_card_nine hX a b ha hb hc haf hbf hne
  intro x hx
  have hh:=congrArg Subtype.val (hi ⟨x,hx⟩)
  change s*(t*x*t⁻¹)*s⁻¹=x⁻¹ at hh
  calc
    (s*t)*x*(s*t)⁻¹=s*(t*x*t⁻¹)*s⁻¹ := by group
    _ = x⁻¹ := hh
end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree
