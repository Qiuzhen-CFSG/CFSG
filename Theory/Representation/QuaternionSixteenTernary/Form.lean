module
public import Theory.Representation.QuaternionSixteenTernary.Certificate
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Tactic

/-!
# The alternating form in the marked quaternion frame

An alternating form fixed by the quaternion subgroup and negated by the
marked order-four inverter is a scalar multiple of the standard form.
The proof solves five relations between the six alternating coefficients;
no classification of forms or matrix group enumeration is required.

Source: the nontrivial similitude condition in Aschbacher,
*Sporadic Groups* (1994), 45.11, p.248.
-/

public section
namespace Theory.Representation.QuaternionSixteenTernary

@[expose] def standardForm (x y : V) : ZMod 3 := x.1*y.2.1-x.2.1*y.1-x.2.2.1*y.2.2.2+x.2.2.2*y.2.2.1

private theorem form_expansion (B : LinearMap.BilinForm (ZMod 3) V) (x y : V)
    (hAlt : B.IsAlt) :
    B x y =
      (x.1*y.2.1-x.2.1*y.1)*B (e 0) (e 1) +
      (x.1*y.2.2.1-x.2.2.1*y.1)*B (e 0) (e 2) +
      (x.1*y.2.2.2-x.2.2.2*y.1)*B (e 0) (e 3) +
      (x.2.1*y.2.2.1-x.2.2.1*y.2.1)*B (e 1) (e 2) +
      (x.2.1*y.2.2.2-x.2.2.2*y.2.1)*B (e 1) (e 3) +
      (x.2.2.1*y.2.2.2-x.2.2.2*y.2.2.1)*B (e 2) (e 3) := by
  have decomp (v : V) : v=v.1 • e 0+v.2.1 • e 1+v.2.2.1 • e 2+v.2.2.2 • e 3 := by
    ext <;> simp [e]
  conv_lhs => rw [decomp x,decomp y]
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  have h01 := (hAlt.neg_eq (e 0) (e 1)).symm
  have h02 := (hAlt.neg_eq (e 0) (e 2)).symm
  have h03 := (hAlt.neg_eq (e 0) (e 3)).symm
  have h12 := (hAlt.neg_eq (e 1) (e 2)).symm
  have h13 := (hAlt.neg_eq (e 1) (e 3)).symm
  have h23 := (hAlt.neg_eq (e 2) (e 3)).symm
  simp only [hAlt.self_eq_zero,h01,h02,h03,h12,h13,h23]
  ring

theorem form_unique (B : LinearMap.BilinForm (ZMod 3) V) (hAlt : B.IsAlt)
    (hi : ∀ x y, B (qi x) (qi y)=B x y)
    (hj : ∀ x y, B (qj x) (qj y)=B x y)
    (hr : ∀ x y, B (r x) (r y)= -B x y) :
    ∀ x y, B x y=B (e 0) (e 1)*standardForm x y := by
  have formulas :
      qi (e 0)=e 0+e 1 ∧ qi (e 1)=e 0-e 1 ∧
      qi (e 2)=e 2-e 3 ∧ qi (e 3)= -e 2-e 3 ∧
      qj (e 0)=e 3 ∧ qj (e 1)=e 2 ∧
      qj (e 2)= -e 1 ∧ qj (e 3)= -e 0 ∧
      r (e 0)=e 2 ∧ r (e 1)=e 2+e 3 ∧ r (e 2)= -e 0 ∧ r (e 3)=e 0-e 1 := by
    decide +kernel
  rcases formulas with ⟨hi0,hi1,hi2,hi3,hj0,hj1,hj2,hj3,hr0,hr1,hr2,hr3⟩
  have reverse (i j : Fin 4) : B (e i) (e j)= -B (e j) (e i) := (hAlt.neg_eq _ _).symm
  have hb := hr (e 0) (e 2)
  rw [hr0,hr2,map_neg,reverse 2 0,neg_neg] at hb
  have hb0 : B (e 0) (e 2)=0 := by
    have he : (2 : ZMod 3)*B (e 0) (e 2)=0 := by linear_combination hb
    exact (mul_eq_zero.mp he).resolve_left (by decide)
  have he0 : B (e 1) (e 3)=0 := by
    have he := hj (e 0) (e 2)
    rw [hj0,hj2,map_neg,reverse 3 1,neg_neg,hb0] at he
    exact he
  have hd := hr (e 0) (e 3)
  rw [hr0,hr3,map_sub,reverse 2 0,reverse 2 1,hb0,neg_zero,zero_sub,neg_neg] at hd
  have hc := hi (e 0) (e 2)
  rw [hi0,hi2,map_add,LinearMap.add_apply,map_sub,map_sub,hb0,he0,zero_sub,sub_zero] at hc
  have hc0 : B (e 0) (e 3)=0 := by
    have he : (2 : ZMod 3)*B (e 0) (e 3)=0 := by linear_combination hd-hc
    exact (mul_eq_zero.mp he).resolve_left (by decide)
  have hd0 : B (e 1) (e 2)=0 := by simpa only [hc0,neg_zero] using hd
  have hf := hj (e 0) (e 1)
  rw [hj0,hj1,reverse 3 2] at hf
  have hf' : B (e 2) (e 3)= -B (e 0) (e 1) := neg_eq_iff_eq_neg.mp hf
  intro x y
  rw [form_expansion B x y hAlt,hb0,he0,hc0,hd0,hf']
  simp only [mul_zero,add_zero,standardForm]
  ring
end Theory.Representation.QuaternionSixteenTernary
