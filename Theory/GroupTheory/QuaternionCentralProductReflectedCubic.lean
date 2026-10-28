module

public import Theory.GroupTheory.QuaternionCentralProductNineAction
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# A reflected cubic fixes only the central involution in the two-core

A nontrivial cubic fixed by an automorphism interchanging two quaternion
factors acts nontrivially on both factors: otherwise faithfulness of the
paired restrictions makes the cubic trivial.  Its fixed subgroup in each
factor is the center.  A cubic action fixing a product cannot change either
factor by their common central involution, so the fixed subgroup of the
central product is exactly that common center.

Source: Aschbacher, *Sporadic Groups* (1994),45.7(1),printed p.245.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

private theorem cubic_fixed_factors (B C : Subgroup G)
    (hi : Nat.card (B ⊓ C : Subgroup G) = 2) (u : G) (hu3 : u^3=1)
    (huB : u ∈ normalizer (B : Set G)) (huC : u ∈ normalizer (C : Set G))
    (b c : G) (hb : b ∈ B) (hc : c ∈ C) (hfix : u*(b*c)*u⁻¹=b*c) :
    u*b*u⁻¹=b ∧ u*c*u⁻¹=c := by
  let f := MulAut.conj u
  let d := b⁻¹*f b
  have hfb : f b ∈ B := (huB b).mp hb
  have hfc : f c ∈ C := (huC c).mp hc
  have he : f b * f c = b*c := (f.map_mul b c).symm.trans hfix
  have hd : d ∈ B ⊓ C := by
    refine ⟨B.mul_mem (B.inv_mem hb) hfb,?_⟩
    have hd' : d = c*(f c)⁻¹ := by
      apply mul_right_cancel (b := f c)
      change b⁻¹*f b*f c=c*(f c)⁻¹*f c
      rw [mul_assoc,he]
      group
    rw [hd']
    exact C.mul_mem hc (C.inv_mem hfc)
  have huN : u ∈ normalizer ((B⊓C : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨huB,huC⟩
  have hdcomm := normalizer_le_centralizer_of_card_two (B⊓C) hi huN d hd
  have hfd : f d=d := by
    change u*d*u⁻¹=d
    rw [←hdcomm,mul_inv_cancel_right]
  have hd2 : d^2=1 := by
    have h := pow_card_eq_one' (x := (⟨d,hd⟩ : (B⊓C : Subgroup G)))
    rw [hi] at h
    exact congrArg Subtype.val h
  have hfb_eq : f b=b*d := by simp only [d,mul_inv_cancel_left]
  have hf3 : f (f (f b))=b := by
    have hpow : f^3=1 := by change MulAut.conj u ^ 3 = 1; rw [←map_pow,hu3,map_one]
    exact congrArg (fun a : MulAut G => a b) hpow
  have hbe : f b=b := by
    calc
      f b = b*d := hfb_eq
      _ = b*(d^2*d) := by rw [hd2,one_mul]
      _ = f (f (f b)) := by simp only [hfb_eq,map_mul,hfd,pow_two,mul_assoc]
      _ = b := hf3
  refine ⟨hbe,?_⟩
  exact mul_left_cancel (hbe ▸ he)

private theorem nontrivial_restriction_of_factor_swap
    {B C : Subgroup G} (d : QuaternionIndependentCubics B C)
    (t : G) (htB : B.map (MulAut.conj t).toMonoidHom = C)
    (u : d.A) (hune : u ≠ 1) (htu : t*(u:G)*t⁻¹=(u:G)) : d.actionB u ≠ 1 := by
  intro hB
  have huB : (u:G) ∈ centralizer (B : Set G) := by
    intro b hb
    have hh := d.actionB_apply u (⟨b,hb⟩ : B)
    rw [hB] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have hC : d.actionC u = 1 := by
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    rw [d.actionC_apply]
    obtain ⟨b,hb,he⟩ := (show (c:G) ∈ B.map (MulAut.conj t).toMonoidHom from htB.symm ▸ c.property)
    change MulAut.conj t b = (c:G) at he
    have hh := congrArg (MulAut.conj t) (huB b hb)
    rw [map_mul,map_mul,show MulAut.conj t (u:G)=(u:G) from htu,he] at hh
    change (u:G)*(c:G)*(u:G)⁻¹=(c:G)
    rw [←hh,mul_inv_cancel_right]
  exact hune (d.faithful (by
    apply Prod.ext
    · simpa only [MonoidHom.prod_apply,Prod.fst_one,map_one] using hB
    · simpa only [MonoidHom.prod_apply,Prod.snd_one,map_one] using hC))

theorem QuaternionIndependentCubics.fixed_core_of_factor_swap [Finite G]
    {B C : Subgroup G} (d : QuaternionIndependentCubics B C)
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hi : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀b∈B,∀c∈C,b*c=c*b)
    (t : G) (htB : B.map (MulAut.conj t).toMonoidHom = C)
    (htC : C.map (MulAut.conj t).toMonoidHom = B)
    (u : d.A) (hune : u ≠ 1) (htu : t*(u:G)*t⁻¹=(u:G)) :
    (B⊔C) ⊓ centralizer ({(u:G)} : Set G) = B⊓C := by
  let : IsElementaryAbelian 3 d.A := d.elementary
  have hu3 : u^3=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 3 d.A) u
  have hu3G : (u:G)^3=1 := congrArg Subtype.val hu3
  have hBu : d.actionB u ≠ 1 := nontrivial_restriction_of_factor_swap d t htB u hune htu
  have hCu : d.actionC u ≠ 1 := by
    intro hCeq
    apply hBu
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [d.actionB_apply]
    obtain ⟨c,hc,he⟩ := (show (b:G) ∈ C.map (MulAut.conj t).toMonoidHom from htC.symm ▸ b.property)
    have hcfix := d.actionC_apply u (⟨c,hc⟩ : C)
    rw [hCeq] at hcfix
    change c=(u:G)*c*(u:G)⁻¹ at hcfix
    change MulAut.conj t c = (b:G) at he
    have hh := congrArg (MulAut.conj t) (mul_inv_eq_iff_eq_mul.mp hcfix.symm)
    rw [map_mul,map_mul,show MulAut.conj t (u:G)=(u:G) from htu,he] at hh
    change (u:G)*(b:G)*(u:G)⁻¹=(b:G)
    rw [hh,mul_inv_cancel_right]
  have huN : (u:G) ∈ normalizer ((B⊓C : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨d.normalizes_left u.property,d.normalizes_right u.property⟩
  apply le_antisymm
  · intro q hq
    have hnorm : C ≤ normalizer (B : Set G) :=
      (show C≤centralizer (B:Set G) from fun c hc b hb=>hcomm b hb c hc).trans (centralizer_le_normalizer _)
    have hp : q∈(B:Set G)*(C:Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left B C hnorm]
      exact hq.1
    obtain ⟨b,hb,c,hc,rfl⟩ := hp
    obtain ⟨hbf,hcf⟩ := cubic_fixed_factors B C hi u hu3G
      (d.normalizes_left u.property) (d.normalizes_right u.property) b c hb hc
      (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hq.2).symm)
    have hbZ : b∈(center B).map B.subtype := by
      refine ⟨⟨b,hb⟩,?_,rfl⟩
      apply QuaternionGroup.fixed_mem_center_of_cube_eq_one_ne_one_of_equiv hB.some (d.actionB u)
        (by rw [←map_pow,hu3,map_one]) hBu
      exact Subtype.ext ((d.actionB_apply u ⟨b,hb⟩).trans hbf)
    have hcZ : c∈(center C).map C.subtype := by
      refine ⟨⟨c,hc⟩,?_,rfl⟩
      apply QuaternionGroup.fixed_mem_center_of_cube_eq_one_ne_one_of_equiv hC.some (d.actionC u)
        (by rw [←map_pow,hu3,map_one]) hCu
      exact Subtype.ext ((d.actionC_apply u ⟨c,hc⟩).trans hcf)
    rw [←intersection_eq_factor_center B C hB hi hcomm] at hbZ
    rw [←intersection_eq_factor_center C B hC (by simpa [inf_comm] using hi)
      (fun c hc b hb=>(hcomm b hb c hc).symm),inf_comm C B] at hcZ
    exact (B⊓C).mul_mem hbZ hcZ
  · exact le_inf (inf_le_left.trans le_sup_left)
      (fun q hq=>mem_centralizer_singleton_iff.mpr
        (normalizer_le_centralizer_of_card_two (B⊓C) hi huN q hq))
end Subgroup
