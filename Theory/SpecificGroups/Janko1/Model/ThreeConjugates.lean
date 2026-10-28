module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Mathlib.Tactic.Group

/-!
# Three conjugates of any J₁ involution generate the group

For the literal ATLAS generators, the product of `a`, `b*a*b⁻¹`, and
`b⁻¹*a*b` is `(a*b)^3`. Since `(a*b)^7 = 1`, its fifth power recovers
`a*b`, hence also `b`. The certified single involution class transports
this explicit generation statement to any involution. This argument needs
no additional finite computation and no simplicity certificate.

The matrices and checked relations are attributed in `Model.Basic`.
This proves the J₁ involution case of Revin–Zavarnitsine, *Conjugate generation
of sporadic almost simple groups*, arXiv:2505.05173v2, Theorem 1; its source
application is the three-conjugate degree bound in Aschbacher–Smith K.4.
-/

namespace Janko1
open Subgroup

/-- Three conjugates of the standard involution recover both ATLAS generators. -/
public theorem standard_three_generate : zpowers a ⊔ zpowers (b * a * b⁻¹) ⊔ zpowers (b⁻¹ * a * b) = ⊤ := by
  let H := zpowers a ⊔ zpowers (b * a * b⁻¹) ⊔ zpowers (b⁻¹ * a * b)
  have h₀ : a ∈ H := mem_sup_left (mem_sup_left (mem_zpowers a))
  have h₁ : b * a * b⁻¹ ∈ H := mem_sup_left (mem_sup_right (mem_zpowers _))
  have h₂ : b⁻¹ * a * b ∈ H := mem_sup_right (mem_zpowers _)
  have hb : b⁻¹ * b⁻¹ = b := by
    apply (mul_right_inj b).mp
    calc
      _ = b⁻¹ := by group
      _ = b * b := by
        apply inv_eq_of_mul_eq_one_right
        simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using b_pow_three
  have hp : (a * b) ^ 3 ∈ H := by
    have he : a * (b * a * b⁻¹) * (b⁻¹ * a * b) = (a * b) ^ 3 := by
      calc
        _ = a * b * a * (b⁻¹ * b⁻¹) * a * b := by group
        _ = (a * b) ^ 3 := by rw [hb]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    exact he ▸ H.mul_mem (H.mul_mem h₀ h₁) h₂
  have hab : a * b ∈ H := by
    have he : ((a * b) ^ 3) ^ 5 = a * b := by
      rw [← pow_mul]
      calc
        (a * b) ^ (3 * 5) = ((a * b) ^ 7) ^ 2 * (a * b) := by
          rw [← pow_mul, ← pow_succ]
        _ = a * b := by rw [ab_pow_seven, one_pow, one_mul]
    exact he ▸ H.pow_mem hp 5
  have hbH : b ∈ H := by simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem h₀) hab
  change H = ⊤
  apply top_unique
  rw [← closure_pair_eq_top, closure_le]
  rintro x (rfl | hx)
  · exact h₀
  · rw [Set.mem_singleton_iff.mp hx]
    exact hbH
/-- Every involution of the actual J₁ matrix group has three conjugates generating it. -/
public theorem three_involution_conjugates (t : Model) (ht : orderOf t = 2) :
    ∃ g h : Model, zpowers t ⊔ zpowers (g * t * g⁻¹) ⊔ zpowers (h * t * h⁻¹) = ⊤ := by
  obtain ⟨u, hu⟩ := involution_fusion_of_card card_model t ht
  refine ⟨u⁻¹ * b * u, u⁻¹ * b⁻¹ * u, ?_⟩
  have he := congrArg (fun H : Subgroup Model => H.map (MulAut.conj u⁻¹).toMonoidHom)
    standard_three_generate
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, map_top_of_surjective _ (MulAut.conj u⁻¹).surjective] at he
  have ha : u⁻¹ * a * u = t := by rw [← hu]; group
  have hb : u⁻¹ * (b * a * b⁻¹) * u =
      (u⁻¹ * b * u) * t * (u⁻¹ * b * u)⁻¹ := by rw [← hu]; group
  have hbi : u⁻¹ * (b⁻¹ * a * b) * u =
      (u⁻¹ * b⁻¹ * u) * t * (u⁻¹ * b⁻¹ * u)⁻¹ := by rw [← hu]; group
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, ha, hb, hbi] using he

end Janko1
