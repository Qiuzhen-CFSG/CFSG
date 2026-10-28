module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.FiveExclusion
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.ExceptionalFixed

/-!
# Diagonal involutions are outside the original z-class

An involution outside the natural S6 subgroup of Aut(A6) fixes a D10.
Lift a five-element of this fixed subgroup through the original cubic kernel.
Cubing provides an element of order five, and its central cubic commutator
with the involution is killed by the fifth power. The resulting actual fixed
five-element in C_G(B) applies the source five-centralizer obstruction.

Source: Aschbacher–Smith J.2.7(7), printed p.436 (PDF p.447).
-/

open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

open scoped commutatorElement
lemma commute_of_cubic_commutator_of_fifth_power (u x : G) (hx : x∈c.GB)
    (hmod : ⁅u,x⁆∈c.B) (hx5 : x^5=1) : Commute u x := by
  let b := ⁅u,x⁆
  have hb : b∈c.B := hmod
  have hb3 : b^3=1 := by
    have h := pow_card_eq_one' (x := (⟨b,hb⟩:c.B))
    rw [SourceCompletion.B_card c] at h
    exact congrArg Subtype.val h
  have hux : u*x*u⁻¹=b*x := by dsimp [b,commutatorElement_def];group
  have hbx : Commute b x := hx b hb
  have hb5 : b^5=1 := by
    have h : (b*x)^5=1 := by rw [←hux,conj_pow,hx5];group
    rwa [hbx.mul_pow,hx5,mul_one] at h
  have hb1 : b=1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 5)
      (orderOf_dvd_of_pow_eq_one hb3) (orderOf_dvd_of_pow_eq_one hb5))
  apply mul_inv_eq_iff_eq_mul.mp
  simpa only [hb1,one_mul] using hux

public theorem fixed_five_lift_source (u : c.NB) (a : c.NormalizerQuotient)
    (ha : a∈c.centralizerImage) (ha5 : orderOf a=5)
    (hfix : Commute (c.normalizerQuotientMap u) a) :
    ∃ y∈c.GB, orderOf y=5 ∧ Commute (u:G) y := by
  obtain ⟨x,hx,rfl⟩ := ha
  have hx15 : (x^3)^5=1 := by
    have hk : x^5∈c.normalizerKernel := by
      rw [←c.normalizerQuotientMap_ker]
      change c.normalizerQuotientMap (x^5)=1
      rw [map_pow,←ha5,pow_orderOf_eq_one]
    have hc : Nat.card c.normalizerKernel=3 :=
      (Nat.card_congr (subgroupOfEquivOfLe (le_normalizer : c.B≤c.NB)).toEquiv).trans
        (SourceCompletion.B_card c)
    have h := pow_card_eq_one' (x := (⟨x^5,hk⟩:c.normalizerKernel))
    rw [hc] at h
    have hh := congrArg Subtype.val h
    change (x^5)^3=1 at hh
    simpa only [←pow_mul] using hh
  have hx3ne : x^3≠1 := by
    intro hh
    have hm : (c.normalizerQuotientMap x)^3=1 := by rw [←map_pow,hh,map_one]
    have hd := orderOf_dvd_of_pow_eq_one hm
    rw [ha5] at hd
    norm_num at hd
  have hx3 : orderOf (x^3)=5 := orderOf_eq_prime hx15 hx3ne
  have hx3GB : ((x^3:c.NB):G)∈c.GB := c.GB.pow_mem hx 3
  refine ⟨x^3,hx3GB,(Subgroup.orderOf_coe (x^3)).trans hx3,?_⟩
  apply c.commute_of_cubic_commutator_of_fifth_power (u:G) (x^3) hx3GB
  · have hk : ⁅u,x^3⁆∈c.normalizerQuotientMap.ker := by
      change c.normalizerQuotientMap ⁅u,x^3⁆=1
      simp only [commutatorElement_def,map_mul,map_inv,map_pow]
      exact commutatorElement_eq_one_iff_commute.mpr (hfix.pow_right 3)
    rw [c.normalizerQuotientMap_ker] at hk
    exact hk
  · exact congrArg Subtype.val hx15

public theorem diagonal_fixed_five_source
    (e : c.NormalizerQuotient ≃* AlternatingSix.ShadowLocal.AutA6)
    (hM : c.centralizerImage.map e.toMonoidHom=AlternatingSix.M10.extension)
    (u : c.NB) (hu : orderOf (e (c.normalizerQuotientMap u))=2)
    (hn : e (c.normalizerQuotientMap u)∉AlternatingSix.ShadowLocal.natural) :
    ∃ y∈c.GB, orderOf y=5 ∧ Commute (u:G) y := by
  let β := e (c.normalizerQuotientMap u)
  have hc := AlternatingSix.ShadowLocal.outside_natural_involution_fixed_card β hu hn
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card'
    (G := GLS3.Chapter5.automorphismFixedSubgroup β) 5 (by rw [hc];decide)
  let b : AlternatingSix.ShadowLocal.AutA6 := MulAut.conj (a:AlternatingSix.ShadowLocal.A6)
  have hbM : b∈AlternatingSix.M10.extension :=
    AlternatingSix.M10.Action.inner_le_extension ⟨a,rfl⟩
  have hb5 : orderOf b=5 :=
    (orderOf_injective MulAut.conj AlternatingSix.ShadowLocal.inner_injective _).trans
      ((Subgroup.orderOf_coe a).trans ha)
  have hbfix : Commute β b := by
    have he : β*b*β⁻¹=b := by
      change β * MulAut.conj (a:AlternatingSix.ShadowLocal.A6) * β⁻¹ = _
      have hh : β*(MulAut.conj (a:AlternatingSix.ShadowLocal.A6))*β⁻¹ =
          MulAut.conj (β a) := by ext y;simp
      rw [hh,a.property]
    exact mul_inv_eq_iff_eq_mul.mp he
  have haM : e.symm b∈c.centralizerImage := by
    rw [←hM] at hbM
    obtain ⟨x,hx,hxb⟩ := hbM
    have he : e.symm b=x := by rw [←hxb];exact e.symm_apply_apply x
    exact he ▸ hx
  apply c.fixed_five_lift_source u (e.symm b) haM
  · exact (orderOf_injective e.symm.toMonoidHom e.symm.injective b).trans hb5
  · apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hbfix.eq

public theorem diagonal_not_z_fused_source
    (e : c.NormalizerQuotient ≃* AlternatingSix.ShadowLocal.AutA6)
    (hM : c.centralizerImage.map e.toMonoidHom=AlternatingSix.M10.extension)
    (u : c.NB) (hu : orderOf (e (c.normalizerQuotientMap u))=2)
    (hn : e (c.normalizerQuotientMap u)∉AlternatingSix.ShadowLocal.natural) :
    ¬IsConj (u:G) c.z := by
  obtain ⟨y,hy,h5,hfix⟩ := c.diagonal_fixed_five_source e hM u hu hn
  exact c.not_z_fused_of_fixed_cubic_five_source (u:G) y hy h5 hfix

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
