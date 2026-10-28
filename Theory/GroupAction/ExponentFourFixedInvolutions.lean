module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.Group.Action.End

/-!
# Automorphisms fixing the involutions of an exponent-four abelian group

Let B be a commutative group whose elements have fourth power one.
If a subgroup A of its automorphism group fixes every square-one element
pointwise, then A is elementary abelian of exponent dividing two. Moreover,
every displacement a(b)b⁻¹ has square one. Identity displacements and the
trivial actor subgroup are included, and no finiteness assumption is needed.

An automorphism fixes b², so its displacement has square one and is itself
fixed. Applying the automorphism twice therefore multiplies b by the square
of that displacement, which is one. A group in which every element squares
to one is commutative, by taking the inverse of a product. This gives the
native elementary-abelian conclusion for the supplied subgroup A.

This elementary action fact supports the C₄×C₄ residual-core argument in
Stellmacher (10.1). The actual core, quotient and graph transfers are left
to the Section Ten consumer; no special model or order bound is used here.
-/

namespace MulAut

public theorem elementaryTwo_of_fixed_involutions
    {B : Type*} [CommGroup B]
    (hfour : ∀ b : B, b ^ 4 = 1) (A : Subgroup (MulAut B))
    (hfix : ∀ a ∈ A, ∀ b : B, b ^ 2 = 1 → a b = b) :
    IsElementaryAbelian 2 A ∧
      ∀ a ∈ A, ∀ b : B, (a b * b⁻¹) ^ 2 = 1 := by
  have hdelta (a : MulAut B) (ha : a ∈ A) (b : B) :
      (a b * b⁻¹) ^ 2 = 1 := by
    have hsquare : (b ^ 2) ^ 2 = 1 := by
      rw [← pow_mul]
      exact hfour b
    calc
      (a b * b⁻¹) ^ 2 = a (b ^ 2) * (b ^ 2)⁻¹ := by
        rw [mul_pow, inv_pow, map_pow]
      _ = 1 := by rw [hfix a ha _ hsquare, mul_inv_cancel]
  have hpow (a : A) : a ^ 2 = 1 := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro b
    let d := (a : MulAut B) b * b⁻¹
    have hd : d ^ 2 = 1 := hdelta a a.property b
    have hfixed : (a : MulAut B) d = d := hfix a a.property d hd
    have hproduct : (a : MulAut B) b = d * b := by simp [d]
    change (a : MulAut B) ((a : MulAut B) b) = b
    calc
      (a : MulAut B) ((a : MulAut B) b) = (a : MulAut B) (d * b) := by rw [← hproduct]
      _ = d * (d * b) := by rw [map_mul, hfixed, hproduct]
      _ = b := by rw [← mul_assoc, ← pow_two, hd, one_mul]
  have hinv (a : A) : a⁻¹ = a :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hpow a)
  have helementary : IsElementaryAbelian 2 A := {
    toIsMulCommutative := ⟨⟨fun a b => by
      calc
        a * b = (a * b)⁻¹ := (hinv (a * b)).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by rw [hinv, hinv]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  exact ⟨helementary,hdelta⟩

end MulAut
