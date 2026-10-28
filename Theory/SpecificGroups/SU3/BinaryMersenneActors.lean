module
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Coverage
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Diagonal
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.NumberTheory.BinaryUnitaryDivisors
public import Theory.SpecificGroups.SU3.OuterSolvable

/-!
# Mersenne-order actors in binary unitary automorphism groups

Semilinear coverage makes the 2s-th power of every automorphism diagonal;
its cube is inner. Huppert's projective order formula and the binary
primitive-divisor argument therefore bound every Mersenne order 2ᶜ−1
by c ≤ 2s. Hermitian basis transport retains the actual caller's form.

Source: GLS3, Theorem 2.5.12 and §2.7; Huppert II.10.12.
The bound supplies a sufficient Cartan estimate for Aschbacher--Smith 7.5.2.
-/
public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

private theorem semilinear_pow
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} {σ : F ≃+* F}
    (ha : J.HasUnitarySemilinearForm a σ) (k : ℕ) :
    J.HasUnitarySemilinearForm (a^k) (σ^k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    apply (HasUnitarySemilinearForm.one_iff J).mpr
    refine ⟨1, ?_⟩
    simpa only [J.unitaryConjHom_apply] using (J.unitaryConjHom.map_one).symm
  | succ k ih =>
    simpa only [pow_succ] using ih.mul J hJ ha

/-- The actual semilinear field part is killed by 2s, and the diagonal part by three. -/
theorem binary_power_inner
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2^s)^2)
    (hfixed : Nat.card {x : F // J.conj x = x} = 2^s)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    a^(6*s) ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨σ,ha⟩ := J.semilinear_coverage s hs hJ hcard hfixed a
  have hσ : σ^(2*s) = 1 := by
    have hc : Nat.card (F ≃+* F) = 2*s :=
      FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
        (by simpa only [pow_mul, Nat.mul_comm] using hcard)
    rw [←hc]
    exact pow_card_eq_one'
  have hf := semilinear_pow J hJ ha (2*s)
  rw [hσ] at hf
  obtain ⟨u,hu⟩ := (HasUnitarySemilinearForm.one_iff J).mp hf
  obtain ⟨v,hv⟩ := J.unitaryConj_cube_is_inner u
  rw [show 6*s = (2*s)*3 by omega,pow_mul,hu,hv]
  exact ⟨v,rfl⟩

/-- A binary unitary automorphism order divides the semilinear exponent times
 the projective group order. -/
theorem binary_automorphism_order_dvd
    {s : ℕ} (hs : 2 ≤ s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x : F, J.conj x = x^(2^s))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    orderOf a ∣ 6*s*((2^s)^3+1)*((2^s)^2-1)*(2^s)^3 := by
  have hfixed : Nat.card {x : F // J.conj x = x} = 2^s :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s (by omega) hcard hconj
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^s) hcard hfixed
  let J₀ := OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  let b := MulAut.congr e a
  have hb := binary_power_inner J₀ rfl hs hcard hfixed b
  obtain ⟨x,hx⟩ := hb
  have hd : orderOf b ∣ (6*s)*Nat.card (ProjectiveSpecialUnitaryMatrixGroup J₀) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul,←hx,←map_pow,pow_card_eq_one',map_one]
  obtain ⟨_,_,_,_,_,_,_,_,hc,_⟩ :=
    huppert_II_10_12 J₀ (2^s) hcard hfixed rfl
  have hG : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J₀) ∣
      ((2^s)^3+1)*(2^s)^3*((2^s)^2-1) := by
    rw [hc]
    apply Nat.div_dvd_of_dvd
    have hh : Nat.gcd 3 (2^s+1) ∣ (2^s)^2-1 := by
      rw [Nat.sq_sub_sq (2^s) 1]
      exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _
    exact dvd_mul_of_dvd_right hh _
  have h := hd.trans (Nat.mul_dvd_mul_left (6*s) hG)
  rw [show orderOf b = orderOf a from (MulAut.congr e).orderOf_eq a] at h
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
/-- Every Mersenne-order automorphism of the actual projective group has
exponent at most twice the fixed-field degree. -/
theorem binary_mersenne_automorphism_bound
    {s c : ℕ} (hs : 2 ≤ s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x : F, J.conj x = x^(2^s))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : orderOf a = 2^c-1) : c ≤ 2*s := by
  by_cases hc : c = 0
  · omega
  have ho : Odd (2^c-1) := Nat.Even.sub_odd Nat.one_le_two_pow
    (even_two.pow_of_ne_zero hc) odd_one
  have hcop := (ho.coprime_two_right.pow_right s).pow_right 3
  have hd := J.binary_automorphism_order_dvd hs hcard hconj a
  rw [ha] at hd
  exact Theory.NumberTheory.BinaryUnitaryDivisors.exponent_le_of_dvd hs
    (hcop.dvd_of_dvd_mul_right hd)
end BenderSuzuki.MatrixGroups.HermitianForm
