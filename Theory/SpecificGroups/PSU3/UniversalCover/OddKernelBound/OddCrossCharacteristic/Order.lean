module

public import Theory.SpecificGroups.PSU3.UniversalCover.Projection
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Theory.GroupTheory.PerfectCentralCoverOddPart

/-!
# Projective order and the first three-adic case

Transport to the standard Hermitian form gives the literal PSU₃ order.
When q ≡ −1 modulo three but nine does not divide q+1, its three-part
has order nine. The order-nine Sylow transfer bound therefore excludes
nine from every finite perfect central-cover kernel, including q = 5.
Two polynomial calculations, for q ≡ 2 or 5 modulo nine, check the
numerator modulo 81 before dividing by the scalar-kernel order three.

Source: Huppert II.10.12; Aschbacher–Smith I.1.3(2), I.1.4(2),
printed pp.407–408 (PDF pp.418–419); GLS3 §6.1, Tables 6.1.2–3.
The cases with nine dividing q+1 are not asserted here.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External PerfectCentralCovering
open HermitianForm.OddPrimeSylow.NormalizedOuter

namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic

variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- The exact order, retaining the scalar quotient and arbitrary Gram matrix. -/
theorem card_projective {q : ℕ} (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) :
    Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) =
      (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
  have hf := card_fixed J hcard hconj
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J q hcard hf
  obtain ⟨_, _, _, _, _, _, _, _, hG, _⟩ :=
    huppert_II_10_12 (FormTransport.standardForm J) q hcard hf rfl
  exact (Nat.card_congr e.toEquiv).trans hG

private theorem not_cube_dvd_order {q : ℕ} (hq : 1 < q)
    (hm : q % 3 = 2) (h9 : ¬ 9 ∣ q + 1) :
    ¬ 27 ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
  have hg : Nat.gcd 3 (q + 1) = 3 := Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero (by omega))
  rw [hg]
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  have hthree : 3 ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_left
    apply Nat.dvd_of_mod_eq_zero
    simp [Nat.add_mod, Nat.pow_mod, hm]
  rw [Nat.dvd_div_iff_mul_dvd hthree]
  intro hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  have hs : (q ^ 2 - 1) % 81 = (q ^ 2 + 80) % 81 := by omega
  have hn : q % 9 ≠ 8 := by
    intro he
    exact h9 (Nat.dvd_of_mod_eq_zero (by omega))
  norm_num only [Nat.reduceMul] at hz
  have hz' : ((q ^ 3 + 1) * q ^ 3 * (q ^ 2 + 80)) % 81 = 0 := by
    simpa only [Nat.mul_mod, Nat.mod_mod, hs] using hz
  have hm9 : q % 9 = 2 ∨ q % 9 = 5 := by omega
  have he : q = 9 * (q / 9) + q % 9 := by omega
  rcases hm9 with hm9 | hm9
  all_goals
    rw [he, hm9] at hz'
    ring_nf at hz'
    norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at hz'

/-- The three-primary bound when the three-part of q+1 has order three. -/
theorem not_nine_dvd_kernel_of_not_nine_dvd_add_one {q : ℕ} (hq : 1 < q)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (hm : q % 3 = 2) (h9 : ¬ 9 ∣ q + 1)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ 9 ∣ Nat.card f.toMonoidHom.ker := by
  apply f.not_nine_dvd_card_kernel_of_cube_not_dvd
  rw [card_projective J hcard hconj]
  exact not_cube_dvd_order hq hm h9

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic
