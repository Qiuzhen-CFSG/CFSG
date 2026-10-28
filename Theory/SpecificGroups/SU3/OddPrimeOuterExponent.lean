module
public import Theory.SpecificGroups.SU3.CyclicNormalOuter.PrimeSquares
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Outer exponent of ternary unitary groups over prime fixed fields

The matrix field has prime-square order, so the square of an automorphism
is induced by a unitary matrix. Scalar determinant correction makes its
cube inner. Hermitian basis transport proves the result for the caller's
actual form, using its specified Frobenius conjugation and inherited simplicity.
Source: GLS3, Theorem 2.5.12 and §2.7;
Aschbacher–Smith A.3.18, pp.51–53.
-/

public section
open Subgroup
noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm
open OddPrimeSylow.NormalizedOuter.FormTransport
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
/-- Every automorphism has sixth power inner over an odd prime fixed field,
for the original arbitrary nondegenerate Hermitian form. -/
theorem odd_prime_sixth_power_inner [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {r : ℕ} (hr : r.Prime) (ho : Odd r)
    (hcard : Nat.card E = r ^ 2) (hconj : ∀ x, J.conj x = x ^ r)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    a ^ 6 ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fact r.Prime := ⟨hr⟩
  have hfixed : Nat.card {x : E // J.conj x = x} = r := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj r 1 (by decide)
        (by simpa only [pow_one] using hcard) (by simpa only [pow_one] using hconj)
  obtain ⟨e⟩ := exists_projectiveEquiv J r hcard hfixed
  let J₀ := standardForm J
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) := e.isSimpleGroup_congr.mp inferInstance
  let b := MulAut.congr e a
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J₀))
  obtain ⟨u, hu⟩ := outer_square_mem_unitary_of_odd_prime J₀ rfl hr ho hcard hfixed b
  obtain ⟨v, hv⟩ := J₀.unitaryConj_cube_is_inner u
  have hb : b ^ 6 ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J₀) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (b ^ 6) = 1
    rw [map_pow, show 6 = 2 * 3 from rfl, pow_mul, ← hu]
    change (q (J₀.unitaryConjHom u)) ^ 3 = 1
    rw [← map_pow, J₀.unitaryConjHom_apply, hv]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨v, rfl⟩
  rw [← MulAut.map_innerSubgroup_congr e] at hb
  obtain ⟨z, hz, he⟩ := hb
  exact (show z = a ^ 6 from (MulAut.congr e).injective
    (he.trans (map_pow (MulAut.congr e) a 6).symm)) ▸ hz
end BenderSuzuki.MatrixGroups.HermitianForm

namespace BenderSuzuki.MatrixGroups.HermitianForm
open OddPrimeSylow.NormalizedOuter.FormTransport
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
/-- The norm-one determinant kills the outer action after twice its exponent. -/
theorem odd_prime_unitary_power_inner [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {r : ℕ} (hr : r.Prime) (ho : Odd r)
    (hcard : Nat.card E = r ^ 2) (hconj : ∀ x, J.conj x = x ^ r)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    a ^ (2 * (r + 1)) ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fact r.Prime := ⟨hr⟩
  have hfixed : Nat.card {x : E // J.conj x = x} = r := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj r 1 (by decide)
        (by simpa only [pow_one] using hcard) (by simpa only [pow_one] using hconj)
  obtain ⟨e⟩ := exists_projectiveEquiv J r hcard hfixed
  let J₀ := standardForm J
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) := e.isSimpleGroup_congr.mp inferInstance
  let b := MulAut.congr e a
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J₀))
  obtain ⟨u, hu⟩ := outer_square_mem_unitary_of_odd_prime J₀ rfl hr ho hcard hfixed b
  have hdet : Matrix.GeneralLinearGroup.det u.val ^ (r + 1) = 1 := by
    apply Units.ext
    have hh := J₀.unitary_det_norm_one u
    change J.conj _ * _ = 1 at hh
    rw [hconj, ← pow_succ] at hh
    exact hh
  let v : J₀.specialSubgroup := ⟨u.val ^ (r + 1), J₀.unitarySubgroup.pow_mem u.property _, by
    change Matrix.GeneralLinearGroup.det (u.val ^ (r + 1)) = 1
    simpa only [map_pow] using hdet⟩
  have hb : b ^ (2 * (r + 1)) ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J₀) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (b ^ (2 * (r + 1))) = 1
    rw [map_pow, pow_mul, ← hu]
    change (q (J₀.unitaryConjHom u)) ^ (r + 1) = 1
    rw [← map_pow, ← map_pow]
    change q (J₀.unitaryConjHom ⟨v.val, v.property.1⟩) = 1
    rw [J₀.unitaryConjHom_apply, J₀.unitaryConj_special_is_inner]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨J₀.specialToProjective v, rfl⟩
  rw [← MulAut.map_innerSubgroup_congr e] at hb
  obtain ⟨z, hz, he⟩ := hb
  exact (show z = a ^ (2 * (r + 1)) from (MulAut.congr e).injective
    (he.trans (map_pow (MulAut.congr e) a (2 * (r + 1))).symm)) ▸ hz
end BenderSuzuki.MatrixGroups.HermitianForm
