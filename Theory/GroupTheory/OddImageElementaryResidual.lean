module
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.OrderOfElement
/-!
# Odd images above an elementary cubic residual quotient

Suppose O²(A)/O₂(O²(A)) has exponent dividing three. An element of A
has a two-power taking it into O²(A), its cube then lies in that residual's
two-core, and a further two-power kills it. Every homomorphism from a
subgroup of A to an odd-order group therefore has image of exponent three.

This retains both successive kernels and does not assume the subgroup
normal in A. The original point stabilizer in Aschbacher--Smith 12.6.31,
printed pp.836--837, supplies the intended torus-action application.
-/

public section
open Subgroup
namespace Subgroup
variable {A Q : Type*} [Group A] [Finite A] [Group Q]

/-- Every odd-order image of any subgroup has exponent dividing three. -/
theorem odd_image_cube_of_residual_quotient
    (hthree : ∀ x : pResidual 2 A ⧸ pCore 2 (pResidual 2 A), x ^ 3 = 1)
    (Y : Subgroup A) (f : Y →* Q) (hodd : Odd (Nat.card Q)) (y : Y) :
    f y ^ 3 = 1 := by
  obtain ⟨a, ha⟩ := (pCore_isPGroup (p := 2) (G := pResidual 2 A)).exists_card_eq
  obtain ⟨b, hb⟩ := (isPGroup_quotient_pResidual (G := A) 2).exists_card_eq
  have hm : (y : A) ^ (2 ^ b) ∈ pResidual 2 A := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pResidual 2 A) ((y : A) ^ (2 ^ b)) = 1
    rw [map_pow, ←hb]
    exact pow_card_eq_one'
  let r : pResidual 2 A := ⟨(y : A) ^ (2 ^ b), hm⟩
  have hr : r ^ 3 ∈ pCore 2 (pResidual 2 A) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 (pResidual 2 A)) (r ^ 3) = 1
    rw [map_pow]
    exact hthree _
  have hp : (r ^ 3) ^ (2 ^ a) = 1 := by
    have h := congrArg (fun u : pCore 2 (pResidual 2 A) => (u : pResidual 2 A))
      (pow_card_eq_one' (x := (⟨r ^ 3, hr⟩ : pCore 2 (pResidual 2 A))))
    simpa only [ha, coe_pow, coe_one] using h
  have hp' : (((y : A) ^ (2 ^ b)) ^ 3) ^ (2 ^ a) = 1 :=
    congrArg (fun u : pResidual 2 A => (u : A)) hp
  have hy : y ^ (3 * 2 ^ (b+a)) = 1 := by
    apply Subtype.ext
    change (y : A) ^ (3 * 2 ^ (b+a)) = 1
    rw [←pow_mul, ←pow_mul] at hp'
    convert hp' using 1
    congr 1
    rw [pow_add]
    ring
  have hf : f y ^ (3 * 2 ^ (b+a)) = 1 := by rw [←map_pow,hy,map_one]
  have hc : Nat.Coprime (orderOf (f y)) (2 ^ (b+a)) :=
    (hodd.coprime_two_right.coprime_dvd_left (_root_.orderOf_dvd_natCard (f y))).pow_right _
  exact orderOf_dvd_iff_pow_eq_one.mp ((hc.dvd_mul_right).mp (orderOf_dvd_of_pow_eq_one hf))
end Subgroup
