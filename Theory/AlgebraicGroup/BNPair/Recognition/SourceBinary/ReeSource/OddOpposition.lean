module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.OddReflection

/-!
# Opposition forced by perpendicular Cartan kernels

For commuting involutions on an odd abelian group, if the fixed subgroup
of their product is the inverted subgroup of the first involution, the
second involution inverts the whole group. The proof first kills its fixed
subgroup using the first involution, then applies this to x times its image.

This is the Cartan calculation used below to extend the perpendicular-root
kernel identities in Fong--Seitz I (6H)(a), p.51, to the longest Weyl element.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource.OddReflection
variable {A : Type*} [CommGroup A]

theorem inversion_of_perpendicular_fixed
    (σ κ : MulAut A) (hσ : Function.Involutive σ) (hκ : Function.Involutive κ)
    (hc : ∀ x, κ (σ x) = σ (κ x)) (ho : Nat.Coprime 2 (Nat.card A))
    (hperp : ∀ x, κ (σ x) = x ↔ σ x = x⁻¹) :
    ∀ x, κ x = x⁻¹ := by
  have hfixed (x : A) (hx : κ x = x) : x = 1 := by
    let u := x * σ x
    have huσ : σ u = u := by dsimp only [u]; rw [map_mul, hσ x, mul_comm]
    have huκ : κ u = u := by simp only [u, map_mul, hc, hx]
    have huinv := (hperp u).mp (by rw [huσ, huκ])
    have hu : u = 1 := by
      have hu2 : u^2 = 1 := by
        rw [pow_two]
        exact (congrArg (· * u) (huσ.symm.trans huinv)).trans (inv_mul_cancel u)
      exact ho.symm.pow_left_bijective.injective (hu2.trans (one_pow 2).symm)
    have hxσ : σ x = x⁻¹ := (inv_eq_of_mul_eq_one_right hu).symm
    have hxp := (hperp x).mpr hxσ
    rw [hc, hx] at hxp
    have hx2 : x^2 = 1 := by
      rw [pow_two]
      exact (congrArg (· * x) (hxp.symm.trans hxσ)).trans (inv_mul_cancel x)
    exact ho.symm.pow_left_bijective.injective (hx2.trans (one_pow 2).symm)
  intro x
  have he := hfixed (x*κ x) (by rw [map_mul, hκ, mul_comm])
  exact (inv_eq_of_mul_eq_one_right he).symm

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource.OddReflection
