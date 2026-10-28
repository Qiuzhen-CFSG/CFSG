module
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Coset.Card

/-!
# Fixed and inverted factors of an odd abelian group

An involutory automorphism of an odd abelian group splits it as the
internal direct product of its fixed and inverted subgroups. Unique
square roots give both factors and show that the inverted subgroup is
exactly the image of x ↦ x⁻¹σ(x), not merely an overgroup of that image.
The multiplication equivalence retains the actual factors.

This is the coprime involution decomposition used for the source Cartan
in Fong–Seitz I, proof of (6H)(a), p.51. CartanReflection applies it to
the literal source normalizer action; no rank-one model is used here.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace OddReflection
variable {A : Type*} [CommGroup A] (σ : MulAut A)

def fixed : Subgroup A := σ.toMonoidHom.eqLocus (MonoidHom.id A)
def inverted : Subgroup A := σ.toMonoidHom.eqLocus invMonoidHom

@[simp] theorem mem_fixed (x : A) : x ∈ fixed σ ↔ σ x = x := Iff.rfl
@[simp] theorem mem_inverted (x : A) : x ∈ inverted σ ↔ σ x = x⁻¹ := Iff.rfl

def displacement : A →* A where
  toFun x := x⁻¹ * σ x
  map_one' := by simp
  map_mul' x y := by simp only [mul_inv_rev, map_mul]; ac_rfl

@[simp] theorem displacement_apply (x : A) : displacement σ x = x⁻¹ * σ x := rfl

theorem displacement_ker : (displacement σ).ker = fixed σ := by
  ext x
  change x⁻¹ * σ x = 1 ↔ σ x = x
  rw [inv_mul_eq_one, eq_comm]

variable (hσ : Function.Involutive σ) (hodd : Nat.Coprime 2 (Nat.card A))

include hodd in
theorem fixed_disjoint_inverted : Disjoint (fixed σ) (inverted σ) := by
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  intro x hx
  have he : x = x⁻¹ := hx.1.symm.trans hx.2
  have hx2 : x^2 = 1 := by rw [pow_two]; exact (congrArg (x * ·) he).trans (mul_inv_cancel x)
  exact hodd.symm.pow_left_bijective.injective (hx2.trans (one_pow 2).symm)

include hσ hodd in
theorem displacement_range : (displacement σ).range = inverted σ := by
  apply le_antisymm
  · rintro x ⟨y,rfl⟩
    change σ (y⁻¹ * σ y) = (y⁻¹ * σ y)⁻¹
    rw [map_mul, map_inv, hσ y, mul_inv_rev, inv_inv]
  · intro x hx
    obtain ⟨y,hy⟩ := hodd.symm.pow_left_bijective.surjective x
    change y^2 = x at hy
    have hyinv : σ y = y⁻¹ := by
      apply hodd.symm.pow_left_bijective.injective
      change (σ y)^2 = (y⁻¹)^2
      rw [← map_pow, hy, (mem_inverted σ x).mp hx, inv_pow, hy]
    refine ⟨y⁻¹, ?_⟩
    rw [displacement_apply, inv_inv, map_inv, hyinv, inv_inv, ← pow_two, hy]

include hσ hodd in
theorem fixed_sup_inverted : fixed σ ⊔ inverted σ = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨y,hy⟩ := hodd.symm.pow_left_bijective.surjective x
  have hf : y * σ y ∈ fixed σ := by
    change σ (y * σ y) = y * σ y
    rw [map_mul, hσ y, mul_comm]
  have hi : y * (σ y)⁻¹ ∈ inverted σ := by
    change σ (y * (σ y)⁻¹) = (y * (σ y)⁻¹)⁻¹
    rw [map_mul, map_inv, hσ y, mul_inv_rev, inv_inv]
  have he : (y * σ y) * (y * (σ y)⁻¹) = x := by
    calc
      _ = y*y := by simp [mul_assoc, mul_left_comm]
      _ = x := by rwa [← pow_two]
  exact he ▸ mul_mem_sup hf hi

def product : fixed σ × inverted σ →* A where
  toFun p := p.1 * p.2
  map_one' := one_mul _
  map_mul' x y := by change (_ * _) * (_ * _) = (_ * _) * (_ * _); ac_rfl

include hσ hodd in
theorem product_bijective : Function.Bijective (product σ) := by
  constructor
  · intro p q hpq
    exact mul_injective_of_disjoint (fixed_disjoint_inverted σ hodd) hpq
  · intro x
    have hx : x ∈ fixed σ ⊔ inverted σ := fixed_sup_inverted σ hσ hodd ▸ mem_top x
    obtain ⟨a,ha,b,hb,he⟩ := mem_sup.mp hx
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩), he⟩

def productEquiv : fixed σ × inverted σ ≃* A :=
  MulEquiv.ofBijective (product σ) (product_bijective σ hσ hodd)

@[simp] theorem productEquiv_apply (a : fixed σ) (b : inverted σ) :
    productEquiv σ hσ hodd (a,b) = (a : A) * b := rfl

include hσ hodd in
theorem card_product : Nat.card A = Nat.card (fixed σ) * Nat.card (inverted σ) := by
  rw [← Nat.card_congr (productEquiv σ hσ hodd).toEquiv, Nat.card_prod]
end OddReflection
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
