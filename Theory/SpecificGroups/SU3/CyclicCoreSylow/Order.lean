module

public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Mathlib.GroupTheory.PGroup

/-!
# The nondefining two-part of the projective unitary order

For p-1 with exact two-part 2^(n+2), every two-subgroup of PSU₃(p)
has order at most 2^(n+4). Factor the numerator of the checked projective
order formula as (p+1)² p³ (p²-p+1) (p-1). Its remaining factor is odd;
the projective scalar divisor divides that numerator. Coprimality removes
the odd factor from the order of each two-subgroup.

Source: Huppert II.10.12; Alperin–Brauer–Gorenstein II.2 Lemma 1,
article p.17; Aschbacher–Smith A.3.21(b), printed p.55.
-/

public section

open Matrix Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.CyclicCoreSylow
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

include hJ in
/-- The exact two-part of the PSU₃ order bounds every literal two-subgroup.
The odd projective scalar divisor can only decrease the order. -/
theorem two_subgroup_card_le {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (n : ℕ) (hdiv : 2 ^ (n + 2) ∣ p - 1) (hodd : Odd ((p - 1) / 2 ^ (n + 2)))
    (R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hR : IsPGroup 2 R) :
    Nat.card R ≤ 2 ^ (n + 4) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa using hcard) (by simpa using hc)
  obtain ⟨_, _, _, _, _, _, _, _, hGcard, _⟩ := huppert_II_10_12 J p hcard hfixed hJ
  have hsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    simpa only [one_pow, mul_comm] using Nat.sq_sub_sq p 1
  have hden : Nat.gcd 3 (p + 1) ∣ (p ^ 3 + 1) * p ^ 3 * (p ^ 2 - 1) := by
    rw [hsq]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (Nat.gcd_dvd_right 3 (p + 1)) _) _
  have hRd : Nat.card R ∣ (p ^ 3 + 1) * p ^ 3 * (p ^ 2 - 1) :=
    R.card_subgroup_dvd_card.trans (by rw [hGcard]; exact Nat.div_dvd_of_dvd hden)
  have hfour : 4 ∣ p - 1 := (show 4 ∣ 2 ^ (n + 2) by
    exact ⟨2 ^ n, by ring⟩).trans hdiv
  have hp1 := hp.one_le
  have hplus : p + 1 = 2 * ((p + 1) / 2) := by
    have := Nat.odd_iff.mp ho
    omega
  have hplusodd : Odd ((p + 1) / 2) := by
    rw [Nat.odd_iff]
    omega
  have hminus : p - 1 = 2 ^ (n + 2) * ((p - 1) / 2 ^ (n + 2)) :=
    (Nat.mul_div_cancel' hdiv).symm
  have hfactor : p ^ 3 + 1 = (p + 1) * (p * (p - 1) + 1) := by
    have he := Nat.sub_add_cancel hp1
    nlinarith [congrArg (fun t : ℕ => p * p * t) he]
  have hfactorodd : Odd (p * (p - 1) + 1) := by
    apply Even.add_one
    apply Even.mul_left
    exact even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 4) hfour)
  let d := ((p + 1) / 2) ^ 2 * p ^ 3 * (p * (p - 1) + 1) * ((p - 1) / 2 ^ (n + 2))
  have hd : Odd d := ((hplusodd.pow.mul ho.pow).mul hfactorodd).mul hodd
  have he : (p ^ 3 + 1) * p ^ 3 * (p ^ 2 - 1) = 2 ^ (n + 4) * d := by
    rw [hfactor, hsq]
    nth_rw 2 [hminus]
    rw [hplus]
    dsimp [d]
    ring
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hcop : (Nat.card R).Coprime d := by rw [hk]; exact hd.coprime_two_left.pow_left k
  apply Nat.le_of_dvd (by positivity : 0 < 2 ^ (n + 4))
  exact hcop.dvd_of_dvd_mul_right (he ▸ hRd)
end BenderSuzuki.MatrixGroups.HermitianForm.CyclicCoreSylow
