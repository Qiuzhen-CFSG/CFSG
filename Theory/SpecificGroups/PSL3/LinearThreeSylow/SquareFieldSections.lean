module
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order

/-!
# Simple-section obstructions for PSL₃ over a binary square field

The upper unitriangular group supplies a nontrivial square. The exact
projective order, with its scalar divisor retained, is divisible by both
3 and 7 when the field has order 2^(2n). These are the intrinsic model
facts used by the Hermitian odd-normalizer parabolic exclusion.

Source: Aschbacher--Smith F.1.12(I), printed pp.262--264, applied in
4.4.12, pp.621--622 (refs/quasithin.pdf).
-/

public noncomputable section

open Subgroup
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry

namespace Matrix.PSL3.LinearThree

/-- The actual binary projective group has a two-subgroup with a nontrivial square. -/
theorem not_two_exponent {S E : Type*} [Group S]
    [Field E] [Finite E] [CharP E 2] (e : S ≃* PSL(3,E))
    {n : ℕ} (hcard : Nat.card E = 2 ^ n) :
    ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1 := by
  intro hS
  let f := e.symm.toMonoidHom.comp (unipotent E).subtype
  have hi : Function.Injective f := e.symm.injective.comp (unipotent E).subtype_injective
  let x := unipotentEquiv E (⟨1,1,0⟩ : U E)
  have hx : x ^ 2 = 1 := by
    apply hi
    simpa only [map_pow,map_one,Subgroup.coe_pow,Subgroup.coe_one,
      MonoidHom.coe_rangeRestrict] using congrArg Subtype.val
      (hS f.range ((unipotent_isTwoGroup E hcard).of_surjective
        f.rangeRestrict f.rangeRestrict_surjective) (f.rangeRestrict x))
  have hu : (⟨1,1,0⟩ : U E) ^ 2 = 1 := (unipotentEquiv E).injective (by
    simpa only [map_pow,map_one] using hx)
  simpa using (square_eq_one_iff E _).mp hu

/-- The scalar quotient still leaves a factor three in the square-field order. -/
theorem square_three_dvd_card {S E : Type*} [Group S]
    [Field E] [Finite E] (e : S ≃* PSL(3,E))
    {n : ℕ} (hcard : Nat.card E = 2 ^ (2*n)) : 3 ∣ Nat.card S := by
  let q := Nat.card E
  have hq : 1 ≤ q := Nat.le_of_lt (Finite.one_lt_card : 1 < Nat.card E)
  have hm : q % 3 = 1 := by
    change Nat.card E % 3 = 1
    rw [hcard,pow_mul]
    norm_num [Nat.pow_mod]
  have ha : 3 ∣ q - 1 := by omega
  have hb : 3 ∣ q ^ 3 - 1 := by
    have ht : q ^ 3 % 3 = 1 := by simp [Nat.pow_mod,hm]
    have hp : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
    omega
  have hc : 3 ∣ q ^ 2 - 1 := by
    have ht : q ^ 2 % 3 = 1 := by simp [Nat.pow_mod,hm]
    have hp : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    omega
  rw [Nat.card_congr e.toEquiv,card_projective]
  change 3 ∣ q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) / Nat.gcd 3 (q-1)
  rw [Nat.gcd_eq_left ha]
  apply (Nat.dvd_div_iff_mul_dvd (dvd_mul_of_dvd_right hc _)).mpr
  exact Nat.mul_dvd_mul (dvd_mul_of_dvd_right hb _) hc

/-- The factor q³ - 1 supplies seven, coprime to the scalar kernel. -/
theorem square_seven_dvd_card {S E : Type*} [Group S]
    [Field E] [Finite E] (e : S ≃* PSL(3,E))
    {n : ℕ} (hcard : Nat.card E = 2 ^ (2*n)) : 7 ∣ Nat.card S := by
  have hm : Nat.card E ^ 3 % 7 = 1 := by
    rw [hcard,← pow_mul,show 2*n*3 = 6*n by omega,pow_mul]
    norm_num [Nat.pow_mod]
  have hp : 1 ≤ Nat.card E ^ 3 := Nat.one_le_pow _ _
    (Nat.le_of_lt (Finite.one_lt_card : 1 < Nat.card E))
  have hd : 7 ∣ Nat.card E ^ 3 - 1 := by omega
  have hd' : 7 ∣ Nat.card PSL(3,E) * Nat.gcd 3 (Nat.card E - 1) := by
    rw [card_projective_mul_scalar]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _
  have hc : Nat.Coprime 7 (Nat.gcd 3 (Nat.card E - 1)) :=
    (by decide : Nat.Coprime 7 3).of_dvd_right (Nat.gcd_dvd_left _ _)
  rw [Nat.card_congr e.toEquiv]
  exact hc.dvd_of_dvd_mul_right hd'

end Matrix.PSL3.LinearThree
