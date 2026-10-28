module

public import Theory.GroupTheory.SpecificGroups.QuaternionEightCubicInverter
public import Theory.GroupTheory.PGroup.UniqueInvolutionClassification
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Adjoining a cubic inverter to a quaternion eight

An actor whose square is the central involution and whose action inverts a
nontrivial cubic produces Q₁₆. The quaternion norm calculation excludes
new involutions in the outside coset. The generated group has order16,
so the unique-involution classification identifies its exact model.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma45.8, p245.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem quaternion_sixteen_of_cubic_inverter (Q:Subgroup G) (e:Q≃*QuaternionGroup 2)
    (z t:G) (hzQ:z∈Q) (hz:orderOf z=2) (ht:t∈normalizer (Q:Set G)) (ht2:t^2=z)
    (c:MulAut Q) (hc:c^3=1) (hcne:c≠1)
    (hinv:Q.normalizerMonoidHom ⟨t,ht⟩*c=c⁻¹*Q.normalizerMonoidHom ⟨t,ht⟩) :
    Nonempty ((Q⊔zpowers t : Subgroup G)≃*QuaternionGroup 4) := by
  let a:=Q.normalizerMonoidHom ⟨t,ht⟩
  have hnorm (q:Q) : (q:G)*(t*(q:G)*t⁻¹)≠z := by
    intro hh
    apply QuaternionGroup.norm_ne_involution_of_inverts_cubic_of_equiv e c a hc hcne hinv
      ⟨z,hzQ⟩ (by rwa [orderOf_mk]) q
    exact Subtype.ext hh
  have hz2:z^2=1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hzI:z⁻¹=z := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hz2)
  have htout:t∉Q := by
    intro hh
    apply hnorm ⟨t⁻¹,Q.inv_mem hh⟩
    change t⁻¹*(t*t⁻¹*t⁻¹)=z
    calc
      _ = (t^2)⁻¹ := by group
      _ = z := by rw [ht2,hzI]
  have ht4:t^4=1 := by rw [show 4=2*2 from rfl,pow_mul,ht2,hz2]
  have hto:orderOf t=4 := orderOf_eq_prime_pow (p:=2) (n:=1)
    (by simpa only [pow_one,ht2,orderOf_eq_one_iff] using
      (show z≠1 from fun hh=>by simp [hh] at hz)) ht4
  let P:=Q⊔zpowers t
  have hform (x:G) (hx:x∈P) : ∃q∈Q,x=q ∨ x=q*t := by
    classical
    change x∈(↑(Q⊔zpowers t):Set G) at hx
    rw [coe_mul_of_right_le_normalizer_left Q (zpowers t) (zpowers_le.mpr ht)] at hx
    obtain ⟨q,hq,w,hw,rfl⟩:=hx
    change w∈zpowers t at hw
    rw [mem_zpowers_iff_mem_range_orderOf,hto] at hw
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hw
    have hi4:=Finset.mem_range.mp hi
    interval_cases i
    · exact ⟨q,hq,Or.inl (by simp)⟩
    · exact ⟨q,hq,Or.inr (by simp)⟩
    · exact ⟨q*z,Q.mul_mem hq hzQ,Or.inl (by rw [ht2])⟩
    · exact ⟨q*z,Q.mul_mem hq hzQ,Or.inr (by rw [pow_succ,ht2,mul_assoc])⟩
  have hQcard:Nat.card Q=8 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
  have hPcard:Nat.card P=16 := by
    let f:Q×Fin 2→P:=fun qi=>⟨(qi.1:G)*t^qi.2.val,
      P.mul_mem (mem_sup_left qi.1.property) (mem_sup_right ((zpowers t).pow_mem (mem_zpowers t) _))⟩
    have hsurj:Function.Surjective f := by
      intro x
      obtain ⟨q,hq,hx|hx⟩:=hform x x.property
      · exact ⟨(⟨q,hq⟩,0),Subtype.ext (by simpa only [f,Fin.val_zero,pow_zero,mul_one] using hx.symm)⟩
      · exact ⟨(⟨q,hq⟩,1),Subtype.ext (by simpa only [f,Fin.val_one,pow_one] using hx.symm)⟩
    have hub:=Nat.card_le_card_of_surjective f hsurj
    rw [Nat.card_prod,hQcard,Nat.card_fin] at hub
    let Q':=Q.subgroupOf P
    have hQc:Nat.card Q'=8 := (Nat.card_congr (subgroupOfEquivOfLe (H:=Q) (K:=P) le_sup_left).toEquiv).trans hQcard
    have hne:Q'≠⊤ := by
      intro hh
      exact htout (show (⟨t,mem_sup_right (mem_zpowers t)⟩:P)∈Q' from hh ▸ mem_top _)
    have hi:=one_lt_index_of_ne_top hne
    have hh:=Q'.card_mul_index
    rw [hQc] at hh
    omega
  have hunique:∃!x:P,orderOf x=2 := by
    refine ⟨⟨z,mem_sup_left hzQ⟩,?_,?_⟩
    · simpa only [orderOf_mk] using hz
    · intro x hx
      have hx2:(x:G)^2=1 := by
        have hh:=pow_orderOf_eq_one x
        rw [hx] at hh
        exact congrArg Subtype.val hh
      obtain ⟨q,hq,hqx|hqx⟩:=hform x x.property
      · apply Subtype.ext
        rw [hqx]
        have hq2:(e ⟨q,hq⟩)^2=1 := by
          have hsub : (⟨q,hq⟩:Q)^2=1 := Subtype.ext (hqx ▸ hx2)
          rw [←map_pow,hsub,map_one]
        have hqne:e ⟨q,hq⟩≠1 := by
          intro hh
          have hq1:q=1 := congrArg Subtype.val (e.injective (hh.trans e.map_one.symm))
          have hx1:x=1 := Subtype.ext (hqx.trans hq1)
          simp [hx1] at hx
        have hez:e ⟨z,hzQ⟩=QuaternionGroup.a 2 := by
          apply (by decide : ∀v:QuaternionGroup 2,v≠1→v^2=1→v=QuaternionGroup.a 2)
          · intro hh
            have hz1:z=1 := congrArg Subtype.val (e.injective (hh.trans e.map_one.symm))
            simp [hz1] at hz
          · have hsub : (⟨z,hzQ⟩:Q)^2=1 := Subtype.ext hz2
            rw [←map_pow,hsub,map_one]
        have heq:e ⟨q,hq⟩=QuaternionGroup.a 2 :=
          (by decide : ∀v:QuaternionGroup 2,v≠1→v^2=1→v=QuaternionGroup.a 2) _ hqne hq2
        exact congrArg Subtype.val (e.injective (heq.trans hez.symm))
      · exfalso
        apply hnorm ⟨q,hq⟩
        change q*(t*q*t⁻¹)=z
        have hh:(q*t)^2=1 := hqx ▸ hx2
        calc
          q*(t*q*t⁻¹) = (q*t)^2*(t^2)⁻¹ := by simp only [pow_two,mul_inv_rev]; group
          _ = z := by rw [hh,ht2,one_mul,hzI]
  have hp:IsPGroup 2 P := IsPGroup.of_card (n:=4) hPcard
  rcases hp.isCyclic_or_quaternion_of_unique_involution hunique with hcyc|⟨n,hn,⟨j⟩⟩
  · let :IsCyclic P:=hcyc
    let inc:Q→*P:=inclusion le_sup_left
    have hcQ:IsMulCommutative Q := by
      constructor
      constructor
      intro q r
      apply inclusion_injective (show Q≤P from le_sup_left)
      simpa only [map_mul] using (mul_comm (inc q) (inc r))
    have hc8:∀q r:QuaternionGroup 2,q*r=r*q := by
      intro q r
      let :IsMulCommutative Q:=hcQ
      obtain ⟨a,rfl⟩:=e.surjective q
      obtain ⟨b,rfl⟩:=e.surjective r
      rw [←map_mul,←map_mul,mul_comm]
    exact False.elim ((by decide : (QuaternionGroup.a 1:QuaternionGroup 2)*QuaternionGroup.xa 0≠QuaternionGroup.xa 0*QuaternionGroup.a 1) (hc8 _ _))
  · have hj:=Nat.card_congr j.toEquiv
    rw [hPcard,Nat.card_eq_fintype_card,QuaternionGroup.card] at hj
    have hpow:2^(n-2)=4 := by omega
    rw [hpow] at j
    exact ⟨j⟩
end Subgroup
