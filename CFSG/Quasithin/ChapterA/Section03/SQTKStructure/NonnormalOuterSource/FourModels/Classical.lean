module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import Theory.SpecificGroups.Classical.BinarySmallThreeRankOuter
public import Theory.SpecificGroups.Classical.ThreeCoverLocalRanks
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank.Divisibility
public import Theory.SpecificGroups.PSL3.DefiningRank
public import Theory.SpecificGroups.SU3.OddDefiningRank
public import Theory.SpecificGroups.SL2.DefiningRank
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Classical source rows with every odd rank at most one

Defining root groups rule out odd-prime signed-three groups and prime-square
PSL₂. Split and norm-one tori rule out the binary degree-three groups, except
PSL₃(2), which is retained through the actual PSL₂(7) equivalence. Every torus
calculation keeps the scalar projection kernel; the chosen prime is different
from three before passing to the projective group.

Source: Aschbacher–Smith A.1.34 and A.3.8(3), pp.29–30 and 45–46.
-/

public noncomputable section
open Matrix Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource.FourModels
open Chapter1.Section02
variable {S : Type*} [Group S] [Finite S]

private theorem odd_prime_divisor {m : ℕ} (ho : Odd m) (hm : 1 < m) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ m := by
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  refine ⟨p,hp,?_,hd⟩
  rcases hp.eq_two_or_odd with rfl | h
  · exact (ho.not_two_dvd_nat hd).elim
  · exact Nat.odd_iff.mpr h

private theorem prime_coprime_three {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) :
    Nat.Coprime p 3 := hp.coprime_iff_not_dvd.mpr (fun hd =>
      h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd))

/-- The full odd PSL₂ row retains exactly prime-field degree. -/
theorem linear_two_odd_model
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p S ≤ 1)
    (p n : ℕ) (hp : p.Prime) (ho : Odd p) (hn : n = 1 ∨ n = 2)
    (hmodel : ClassicalGroup.IsPSL S 2 (p ^ n)) : NonnormalCComponentModel S := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have hlow := SpecialLinearGroup.fieldExponent_le_primeRank_of_projective_injective
    hc e.symm.toMonoidHom e.symm.injective
  have hup := hr p hp ho
  have he : n = 1 := by omega
  subst n
  exact .linear_prime p hp ho ⟨F,inferInstance,inferInstance,by simpa using hc,⟨e⟩⟩

/-- Defining prime rank excludes every odd-prime PSL₃ source row. -/
theorem linear_three_odd_false
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p S ≤ 1)
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL S 3 p) : False := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (f := 1)
    (by simpa only [Nat.card_eq_fintype_card, pow_one] using hc)
  have hlow := PSL3.DefiningRank.two_mul_fieldExponent_le_primeRank F
    (p := p) (e := 1) (by simpa using hc)
  have hup := hr p hp ho
  rw [primeRank_equiv p e] at hup
  omega

/-- Defining prime rank excludes every odd-prime PSU₃ source row. -/
theorem unitary_three_odd_false
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p S ≤ 1)
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU S 3 p) : False := by
  obtain ⟨F, _, _, J, hc, hconj, ⟨e⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective e.symm e.symm.injective
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  have hlow := HermitianForm.OddDefiningRank.two_mul_fieldExponent_le_primeRank J
    (p := p) (e := 1) hp2 (by decide) (by simpa using hc) (by simpa using hconj)
  have hup := hr p hp ho
  rw [primeRank_equiv p e] at hup
  omega

/-- The binary PSL₃ row reduces to its genuine order-168 prime-field alias. -/
theorem linear_three_binary_model
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p S ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (hmodel : ClassicalGroup.IsPSL S 3 (2 ^ n)) :
    NonnormalCComponentModel S := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hmodel
  by_cases h1 : n = 1
  · subst n
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    let : Fintype F := Fintype.ofFinite F
    let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod,pow_one] using hc)
    exact .linear_prime 7 (by decide) (by decide)
      ⟨ZMod 7,inferInstance,inferInstance,by simp,
        ⟨(e.trans (Atlas.fieldEquivPSL 3 eF)).trans
          Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm⟩⟩
  have hthree := hr 3 (by decide) (by decide)
  rw [primeRank_equiv 3 e] at hthree
  have hcop : Nat.Coprime 3 (2 ^ n - 1) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro hd
    have hh := Theory.SpecificGroups.SignedThreeCubicRank.linear_projective_of_three_dvd
      (F := F) (by simpa only [hc] using hd)
    omega
  have hpow : 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ n)
  have he : Even (2 ^ n) := Nat.even_pow.mpr ⟨by decide,by omega⟩
  have ho : Odd (2 ^ n - 1) := Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)
  obtain ⟨p,hp,hpo,hd⟩ := odd_prime_divisor ho (by omega)
  let : Fact p.Prime := ⟨hp⟩
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact Nat.prime_three.coprime_iff_not_dvd.mp hcop hd
  have hunit : 1 ≤ primeRank p Fˣ := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hz
    apply PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    simpa only [Nat.card_units,hc] using hd
  have htorus : 2 ≤ primeRank p (Fˣ × Fˣ) := by
    rw [primeRank_prod_eq_add p]; omega
  have hsl : 2 ≤ primeRank p SL(3,F) := htorus.trans
    (Theory.GroupTheory.primeRank_le_of_injective p (PSL3.CartanActions.torusSL F)
      (PSL3.CartanActions.BorelQuotient.torusSL_injective F))
  have hk : Nat.Coprime p (Nat.card (PSL3.projection F).ker) := by
    apply (prime_coprime_three hp hp3).of_dvd_right
    rw [PSL3.card_projectionKernel]
    exact Nat.gcd_dvd_left 3 (Nat.card F - 1)
  rw [primeRank_eq_of_surjective_of_coprime p (PSL3.projection F)
    (PSL3.projection_surjective F) hk] at hsl
  have hup := hr p hp hpo
  rw [primeRank_equiv p e] at hup
  omega

/-- A norm-one torus rules out every binary PSU₃ source row. -/
theorem unitary_three_binary_false
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p S ≤ 1)
    (n : ℕ) (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSU S 3 (2 ^ n)) : False := by
  obtain ⟨F, _, _, J, hc, hconj, ⟨e⟩⟩ := hmodel
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective e.symm e.symm.injective
  have hthree := hr 3 (by decide) (by decide)
  rw [primeRank_equiv 3 e] at hthree
  have he := Theory.SpecificGroups.Classical.BinarySmallThreeRankOuter.unitary_degree_even
    J (by omega : 0 < n) hc hconj hthree
  have hcop : Nat.Coprime 3 (2 ^ n + 1) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    have hm := Nat.BinaryTorusParity.two_pow_mod_three n
    rw [Nat.even_iff.mp he, if_pos rfl] at hm
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega
  have hpow : 0 < 2 ^ n := pow_pos (by decide) _
  have heq : Even (2 ^ n) := Nat.even_pow.mpr ⟨by decide,by omega⟩
  have hoq : Odd (2 ^ n + 1) := Nat.odd_iff.mpr (by have := Nat.even_iff.mp heq; omega)
  obtain ⟨p,hp,hpo,hd⟩ := odd_prime_divisor hoq (by omega)
  let : Fact p.Prime := ⟨hp⟩
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact Nat.prime_three.coprime_iff_not_dvd.mp hcop hd
  have hsu := Theory.SpecificGroups.Classical.ThreeCoverLocalRanks.binary_unitary_special_primeRank_ge_two
    J (by omega : 0 < n) hp hd hc hconj
  have hker : IsPGroup 3 J.specialToProjective.ker := fun x =>
    ⟨1,by simpa using J.specialToProjective_ker_cube x⟩
  obtain ⟨k,hk⟩ := hker.exists_card_eq
  have hpk : Nat.Coprime p (Nat.card J.specialToProjective.ker) := by
    rw [hk]
    exact (prime_coprime_three hp hp3).pow_right k
  rw [primeRank_eq_of_surjective_of_coprime p J.specialToProjective
    J.specialToProjective_surjective hpk] at hsu
  have hup := hr p hp hpo
  rw [primeRank_equiv p e] at hup
  omega

end CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource.FourModels
