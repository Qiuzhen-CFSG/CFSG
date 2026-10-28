module

public import CFSG.Quasithin.ClassificationModels
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTorus
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTorus.Arithmetic
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTwoLocal
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
public import Theory.FieldTheory.QuadraticFrobeniusFixed
public import Theory.GroupTheory.QuasithinBasic

/-!
# The unitary-five parameter in Theorem D

For q = 2^n other than four there is an odd prime p different from five
dividing q+1. The already constructed diagonal p-torus has rank three in
the actual two-local line parabolic of PSU5(q), contrary to quasithinness.
Orthonormalization transports an arbitrary allowed Hermitian form to the
identity Gram matrix without changing its stored Frobenius involution.

This is the U5 restriction of Aschbacher--Smith A.2.18 (printed p.40) and
Theorem D/14.8.2(1) (printed pp.1078--1079). The proof needs neither the
full U5 Levi decomposition nor an assertion about the 5-primary torus.
-/

namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch

open BenderSuzuki.MatrixGroups
open HermitianForm.IdentityGram

private theorem fixed_card_binary {F : Type*} [Field F] [Finite F]
    {d : ℕ} (J : HermitianForm d F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    Nat.card {x : F // J.conj x = x} = 2 ^ n := by
  classical
  let K := GaloisField 2 (2 * n)
  let : Fintype F := Fintype.ofFinite F
  let : Fintype K := Fintype.ofFinite K
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul]
    congr 1
    omega
  let e : F ≃+* K := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hcard.trans hK.symm)
  let σ := iterateFrobeniusEquiv K 2 n
  have he (x : F) : J.conj x = x ↔ σ (e x) = e x := by
    rw [hconj, iterateFrobeniusEquiv_def, ← map_pow]
    exact e.injective.eq_iff.symm
  exact (Nat.card_congr (e.toEquiv.subtypeEquiv he)).trans
    (GaloisField.card_fixedBy_quadraticFrobenius 2 n (by omega))

/-- Quasithinness alone imposes the exact field exponent on every genuine
PSU5 model, including arbitrary nondegenerate Hermitian forms. -/
public theorem psu_five_exponent_eq_two_of_quasithin
    {G : Type*} [Group G] [Finite G] (hG : IsQuasithin G)
    {n : ℕ} (hn : 0 < n) (hmodel : ClassicalGroup.IsPSU G 5 (2 ^ n)) :
    n = 2 := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective e.symm e.symm.injective
  let : CharP F 2 := by
    let : Fintype F := Fintype.ofFinite F
    apply ringChar.of_eq
    apply (FiniteField.even_card_iff_char_two).mpr
    rw [← Nat.card_eq_fintype_card, hcard]
    have he : Even (2 ^ n) := even_two.pow_of_ne_zero (by omega)
    exact Nat.mod_eq_zero_of_dvd
      (even_iff_two_dvd.mp (he.pow_of_ne_zero (by decide : (2 : ℕ) ≠ 0)))
  obtain ⟨C, hC⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    5 J (2 ^ n) hcard (fixed_card_binary J n hn hcard hconj)
  let ep := projectiveEquiv J C hC
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup (identityGram J)) :=
    Finite.of_injective ep.symm ep.symm.injective
  have hstd : IsQuasithin (ProjectiveSpecialUnitaryMatrixGroup (identityGram J)) :=
    Theory.GroupTheory.isQuasithin_of_equiv (e.trans ep) hG
  have hq : IsPrimePow (2 ^ n) :=
    (isPrimePow_nat_iff _).mpr ⟨2, n, Nat.prime_two, hn, rfl⟩
  have heven : Even (2 ^ n) := even_two.pow_of_ne_zero (by omega)
  have hq4 : 2 ^ n = 4 := by
    by_contra hne
    obtain ⟨p, hp, ho, hd, hp5⟩ :=
      Theory.SpecificGroups.UnitaryFive.exists_odd_prime_ne_five_dvd_succ
        hq heven hne
    have hr := Theory.SpecificGroups.UnitaryFive.primeRank_lineParabolic_ge_of_prime_ne_five
      (identityGram J) rfl hcard hq.one_lt hconj hp hd hp5
    have hb := (Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hstd)
      (Theory.SpecificGroups.UnitaryFive.lineParabolic (identityGram J))
      (Theory.SpecificGroups.UnitaryFive.lineParabolic_isTwoLocal (identityGram J) rfl)
      p hp ho
    exact (Nat.not_succ_le_self 2) (hr.trans hb)
  exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ))) hq4

/-- Actual application to the full D catalogue, with its exact n > 1 bound.
The full catalogue continues to retain the independent general Ree family. -/
public theorem theoremDModel_of_psu_five
    {G : Type*} [Group G] [Finite G] (hG : IsQuasithin G)
    {n : ℕ} (hn : 0 < n) (hmodel : ClassicalGroup.IsPSU G 5 (2 ^ n)) :
    ClassificationModels.IsTheoremDModel G := by
  have hn2 := psu_five_exponent_eq_two_of_quasithin hG hn hmodel
  exact .rank_two n (by omega) (.unitary_five hn2 hmodel)

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
