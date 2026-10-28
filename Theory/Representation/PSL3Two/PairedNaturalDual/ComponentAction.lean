module
public import Theory.Representation.PSL3Two.PairedNaturalDual

/-!
# Covariance of the literal component embeddings

Joint faithfulness identifies conjugation on an embedded factor with its
marked automorphism action. The factor injection and covariance are derived
from the two projection identities, rather than separately assumed.
Source application: Aschbacher--Smith 14.6.24(3), printed pp.1040--1041.
-/

public section
open Subgroup Representation
namespace BinaryLinearThree.NaturalDual.Paired.Marking
variable {H E : Type*} [_root_.Group H] [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : Representation (ZMod 2) H E} (m : Marking ρ)

theorem right_component_injective (κ : Group →* H)
    (hr : ∀ k, m.right (κ k) = MulAut.conj k) : Function.Injective κ := by
  intro x y hxy
  apply MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
  rw [←hr x,←hr y,hxy]

theorem right_component_covariance (hf : Function.Injective ρ) (κ : Group →* H)
    (hl : ∀ k, m.left (κ k) = 1) (hr : ∀ k, m.right (κ k) = MulAut.conj k)
    (a : H) (k : Group) : κ (m.right a k) = a * κ k * a⁻¹ := by
  apply m.joint_injective hf
  apply Prod.ext
  · change m.left (κ (m.right a k)) = m.left (a * κ k * a⁻¹)
    rw [hl,map_mul,map_mul,map_inv,hl,mul_one,mul_inv_cancel]
  · change m.right (κ (m.right a k)) = m.right (a * κ k * a⁻¹)
    rw [hr,map_mul,map_mul,map_inv,hr]
    ext g
    simp only [MulAut.conj_apply,MulAut.mul_apply,map_mul,map_inv]
    simp
end BinaryLinearThree.NaturalDual.Paired.Marking
