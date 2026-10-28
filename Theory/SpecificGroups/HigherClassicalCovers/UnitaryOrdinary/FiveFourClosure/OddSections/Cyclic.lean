module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.Reduction
public import Theory.GroupTheory.PerfectCentralCoverOddPart
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The cyclic odd-prime branches for SU₅(4)

The faithful natural representation places SU₅(4) in GL₅(F₁₆). The latter
has order 2⁴⁰ 3⁶ 5⁶ 7 11 13 17² 31 41 257, so outside 2, 3, 5 and 17
every Sylow subgroup is cyclic. Central transfer excludes these primes
from every finite perfect central covering kernel. This proves the literal
prime-degree local-section contract by contradiction.

For 17, the expected unitary order bound excludes its square and gives the
same result. That bound is retained explicitly until the independent
unitary counting calculation is supplied; no unitary order formula is
inferred from the natural scalar kernel.

Source: Aschbacher--Smith I.1.2 and I.1.4(4), printed pp.407--408 of
`refs/quasithin.pdf`; GLS3 Section 6.1. The ambient linear order is
Mathlib's `Matrix.card_GL_field`.
-/

public section

open Matrix BenderSuzuki.MatrixGroups PerfectCentralCovering
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections
variable {F : Type*} [Field F] [Finite F]

private theorem square_not_dvd_linear_order {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp17 : p ≠ 17) :
    ¬ p^2 ∣ 2^40 * 3^6 * 5^6 * 17^2 * (7*11*13*31*41*257) := by
  have hcop (q : ℕ) (hq : q.Prime) (hpq : p ≠ q) : (p^2).Coprime q :=
    (hp.coprime_iff_not_dvd.mpr (fun hd =>
      hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd))).pow_left 2
  intro h
  have hc : (p^2).Coprime (2^40 * 3^6 * 5^6 * 17^2) :=
    (((hcop 2 (by decide) hp2).pow_right 40).mul_right
      ((hcop 3 (by decide) hp3).pow_right 6)).mul_right
      ((hcop 5 (by decide) hp5).pow_right 6) |>.mul_right
      ((hcop 17 (by decide) hp17).pow_right 2)
  have hs := hc.dvd_mul_left.mp h
  have hd := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hs
  rcases hp.dvd_mul.mp hd with hd | hd
  · rcases hp.dvd_mul.mp hd with hd | hd
    · rcases hp.dvd_mul.mp hd with hd | hd
      · rcases hp.dvd_mul.mp hd with hd | hd
        · rcases hp.dvd_mul.mp hd with hd | hd
          · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp hd
            subst p; norm_num at hs
          · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11)).mp hd
            subst p; norm_num at hs
        · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13)).mp hd
          subst p; norm_num at hs
      · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31)).mp hd
        subst p; norm_num at hs
    · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 41)).mp hd
      subst p; norm_num at hs
  · have he := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 257)).mp hd
    subst p; norm_num at hs

/-- The ambient GL₅(F₁₆) order already excludes every kernel prime except
2, 3, 5 and 17. This does not use a unitary order formula. -/
theorem not_dvd_kernel_of_ne_two_three_five_seventeen
    (J : HermitianForm 5 F) (hF : Nat.card F = 16)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hp5 : p ≠ 5) (hp17 : p ≠ 17)
    {E : Type*} [Group E] [Finite E] (d : Cover E J.specialSubgroup) :
    ¬ p ∣ Nat.card d.toMonoidHom.ker := by
  apply d.not_dvd_card_kernel_of_square_not_dvd
  intro h
  apply square_not_dvd_linear_order (Fact.out : p.Prime) hp2 hp3 hp5 hp17
  have hd := h.trans J.specialSubgroup.card_subgroup_dvd_card
  let : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hF] at hd
  norm_num [Fin.prod_univ_succ] at hd ⊢
  exact hd

/-- The nonexceptional odd-prime local-section contract is discharged by
excluding the literal prime-degree cover. -/
theorem primeLocalSections_of_ne_two_three_five_seventeen
    (J : HermitianForm 5 F) (hF : Nat.card F = 16)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hp5 : p ≠ 5) (hp17 : p ≠ 17) : PrimeLocalSections J p := by
  intro E _ _ d hd
  exact False.elim (not_dvd_kernel_of_ne_two_three_five_seventeen
    J hF hp2 hp3 hp5 hp17 d (hd ▸ dvd_rfl))

/-- The expected SU₅(4) order bound closes the remaining cyclic prime 17. -/
theorem seventeen_primeLocalSections_of_card_dvd
    (J : HermitianForm 5 F)
    (hG : Nat.card J.specialSubgroup ∣ 2^20 * 3^2 * 5^5 * 13 * 17 * 41) :
    PrimeLocalSections J 17 := by
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  intro E _ _ d hd
  have hn := d.not_dvd_card_kernel_of_square_not_dvd (p := 17) (fun h =>
    (by norm_num : ¬ 17^2 ∣ 2^20 * 3^2 * 5^5 * 13 * 17 * 41) (h.trans hG))
  exact False.elim (hn (hd ▸ dvd_rfl))

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections
