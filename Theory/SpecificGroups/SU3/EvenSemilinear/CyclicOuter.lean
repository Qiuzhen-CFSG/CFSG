module

public import Theory.SpecificGroups.SU3.EvenSemilinear
public import Theory.SpecificGroups.SU3.CyclicNormalOuter
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Diagonal
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Cyclic outer groups of binary PSU₃ in even degree

For a ternary unitary group, every element of the diagonal outer image has
cube one by scalar determinant correction. The unitary determinant has norm
one, so the same outer element has `(q + 1)`-st power one. When `q = 2^n`
with `n` even these exponents are coprime, and the diagonal image is trivial.

The proved characteristic-two semilinear coverage makes the quotient by
that image cyclic. A genuine Hermitian basis change transports this result
from the antidiagonal form to any nondegenerate Hermitian form with the same
quadratic Frobenius. Simplicity is inherited from the consumer; no coverage
or outer-group premise remains.

Source: GLS3, Theorem 2.5.12(b,c,d,f) and §2.7,
`refs/KGroup/GLS3/chapter2.tex`; the external unitary case of
Aschbacher–Smith 13.8.20(a), combined manuscript, printed p.954.
-/

public section

open Matrix Subgroup
open BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- The diagonal outer image vanishes when three is coprime to the norm-one
exponent. The existing scalar correction kills cubes; the determinant kills
`q + 1` powers. This needs neither a group-order formula nor finiteness. -/
theorem unitaryOuterHom_range_eq_bot_of_coprime {q : ℕ} (hconj : ∀ x : E, J.conj x = x ^ q)
    (hcop : Nat.Coprime 3 (q + 1)) : J.unitaryOuterHom.range = ⊥ := by
  apply bot_unique
  rintro x ⟨u, rfl⟩
  apply mem_bot.mpr
  have hthree : J.unitaryOuterHom u ^ 3 = 1 := by
    obtain ⟨b, hb⟩ := J.unitaryConj_cube_is_inner u
    change (QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
      (J.unitaryConjHom u)) ^ 3 = 1
    rw [J.unitaryConjHom_apply, ← map_pow, hb]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨b, rfl⟩
  have hdet : GeneralLinearGroup.det u.val ^ (q + 1) = 1 := by
    apply Units.ext
    have h := J.unitary_det_norm_one u
    rw [hconj, ← pow_succ] at h
    exact h
  let v : J.specialSubgroup := ⟨u.val ^ (q + 1),
    J.unitarySubgroup.pow_mem u.property _, by
      change GeneralLinearGroup.det (u.val ^ (q + 1)) = 1
      simpa only [map_pow] using hdet⟩
  have hq : J.unitaryOuterHom u ^ (q + 1) = 1 := by
    rw [← map_pow]
    change QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
      (J.unitaryConjHom ⟨v.val, v.property.1⟩) = 1
    rw [J.unitaryConjHom_apply, J.unitaryConj_special_is_inner]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨J.specialToProjective v, rfl⟩
  apply orderOf_eq_one_iff.mp
  exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd
    (orderOf_dvd_of_pow_eq_one hthree) (orderOf_dvd_of_pow_eq_one hq))

namespace EvenSemilinear

private theorem coprime_three_plus {n : ℕ} (hn : Even n) :
    Nat.Coprime 3 (2 ^ n + 1) := by
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  have hm := Nat.BinaryTorusParity.two_pow_mod_three n
  rw [Nat.even_iff.mp hn, if_pos rfl] at hm
  intro hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  omega

/-- In even binary degree, the standard PSU₃ model has cyclic outer group.
The diagonal contribution is trivial, and all semilinear coverage is proved. -/
theorem standard_outer_isCyclic_of_even [Finite E]
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 1 < n) (heven : Even n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) :
    IsCyclic (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have hcover := semilinear_coverage J hJ (by omega : 2 ≤ n) hcard hconj
  let := J.unitaryOuterHom_range_normal_of_semilinear_coverage hJ hcover
  have hcyc := J.outer_mod_unitary_isCyclic_of_semilinear_coverage hJ hcover
  let e := (QuotientGroup.quotientMulEquivOfEq
    (unitaryOuterHom_range_eq_bot_of_coprime J hconj (coprime_three_plus heven))).trans
      QuotientGroup.quotientBot
  exact e.isCyclic.mp hcyc

open OddPrimeSylow.NormalizedOuter.FormTransport

/-- Any nondegenerate Hermitian form with the specified quadratic Frobenius
has cyclic PSU₃ outer group in even binary degree, assuming the inherited
simplicity of the actual projective image. -/
theorem outer_isCyclic_of_even [Finite E]
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {n : ℕ} (hn : 1 < n) (heven : Even n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) :
    IsCyclic (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  obtain ⟨e⟩ := exists_projectiveEquiv J (2 ^ n) hcard hfixed
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup (standardForm J)) :=
    e.isSimpleGroup_congr.mp inferInstance
  let := standard_outer_isCyclic_of_even (standardForm J) rfl hn heven hcard hconj
  exact (MulAut.outerCongr e).isCyclic.mpr inferInstance

end EvenSemilinear
end BenderSuzuki.MatrixGroups.HermitianForm
