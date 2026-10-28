module
public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionTypes
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Kernel

/-!
# Inner correction for a swapping quaternion involution

Two involutive automorphisms with the same action on U/Z(U) differ by an
inner automorphism. Decompose its conjugating element into the two actual
quaternion factors. Conjugating by the second component makes the actions
agree on the first factor; their squares and factor interchange then force
agreement on the second factor as well.

This is the intrinsic correction used in lifting the normalizer calculation
in Aschbacher–Smith, combined manuscript of 1 March 2004, proof of 14.4.4,
printed p.1007. It does not assert a lift through an extra ambient centralizer.
-/

open Subgroup
open scoped Pointwise
namespace Subgroup.QuaternionCentralProductData
variable {P : Type*} [Group P] [Finite P] (d : QuaternionCentralProductData P)

/-- Two involutive actions with the same central-quotient action, one swapping
the quaternion factors, differ by conjugation by an inner automorphism. -/
public theorem swap_inner_correction (α β : MulAut P) (hα : α ^ 2 = 1)
    (hβ : β ^ 2 = 1) (hswap : d.left.map α.toMonoidHom = d.right)
    (hquot : quotientAut (center P) β = quotientAut (center P) α) :
    ∃ u : P, MulAut.conj u * β * (MulAut.conj u)⁻¹ = α := by
  have hk : quotientAut (center P) (β * α⁻¹) = 1 := by
    rw [map_mul, map_inv, hquot, mul_inv_cancel]
  obtain ⟨t, ht⟩ := (d.quotientAut_eq_one_iff_inner _).mp hk
  have hba : β = MulAut.conj t * α := by rw [ht]; group
  have hn : d.right ≤ normalizer (d.left : Set P) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    exact fun c hc b hb => d.commute b hb c hc
  have htp : t ∈ (d.left : Set P) * (d.right : Set P) := by
    rw [← coe_mul_of_right_le_normalizer_left d.left d.right hn, d.span]
    trivial
  obtain ⟨b, hb, c, hc, rfl⟩ := htp
  let γ := MulAut.conj c * α * (MulAut.conj c)⁻¹
  have hγ : γ ^ 2 = 1 := by dsimp [γ]; rw [pow_two] at hα ⊢; calc
    _ = MulAut.conj c * (α * α) * (MulAut.conj c)⁻¹ := by group
    _ = 1 := by rw [hα]; group
  have heL (x : P) (hx : x ∈ d.left) : β x = γ x := by
    have hcx : c⁻¹ * x * c = x := by
      rw [← d.commute x hx c⁻¹ (d.right.inv_mem hc)]; group
    have hαx : α x ∈ d.right := hswap.le (mem_map_of_mem α.toMonoidHom hx)
    have hcxr : c * α x * c⁻¹ ∈ d.right :=
      d.right.mul_mem (d.right.mul_mem hc hαx) (d.right.inv_mem hc)
    change β x = c * α (c⁻¹ * x * c) * c⁻¹
    rw [hcx, hba]
    change (b*c) * α x * (b*c)⁻¹ = _
    calc
      _ = b * (c * α x * c⁻¹) * b⁻¹ := by group
      _ = c * α x * c⁻¹ := by rw [d.commute b hb _ hcxr]; group
  have hβL : d.left.map β.toMonoidHom = d.right := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change β x ∈ d.right
      rw [heL x hx]
      change c * α (c⁻¹ * x * c) * c⁻¹ ∈ d.right
      have hcfix : c⁻¹ * x * c = x := by
        rw [← d.commute x hx c⁻¹ (d.right.inv_mem hc)]; group
      rw [hcfix]
      exact d.right.mul_mem (d.right.mul_mem hc
        (hswap.le (mem_map_of_mem α.toMonoidHom hx))) (d.right.inv_mem hc)
    · intro y hy
      have hcy : c⁻¹ * y * c ∈ d.right :=
        d.right.mul_mem (d.right.mul_mem (d.right.inv_mem hc) hy) hc
      obtain ⟨x, hx, he⟩ := hswap.ge hcy
      refine ⟨x, hx, ?_⟩
      change β x = y
      rw [heL x hx]
      change c * α (c⁻¹ * x * c) * c⁻¹ = y
      have hcfix : c⁻¹ * x * c = x := by
        rw [← d.commute x hx c⁻¹ (d.right.inv_mem hc)]; group
      rw [hcfix, show α x = c⁻¹ * y * c from he]
      group
  have heR (x : P) (hx : x ∈ d.right) : β x = γ x := by
    obtain ⟨y, hy, rfl⟩ := hβL.ge hx
    have hb2 (z : P) : β (β z) = z := by
      simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun hβ z
    have hg2 (z : P) : γ (γ z) = z := by
      simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun hγ z
    change β (β y) = γ (β y)
    rw [hb2, heL y hy, hg2]
  have heq : β = γ := by
    apply MulEquiv.ext
    have he : d.left ⊔ d.right ≤ β.toMonoidHom.eqLocus γ.toMonoidHom :=
      sup_le heL heR
    rw [d.span] at he
    exact fun x => he (mem_top x)
  refine ⟨c⁻¹, ?_⟩
  rw [heq, map_inv]
  dsimp [γ]
  group
end Subgroup.QuaternionCentralProductData
