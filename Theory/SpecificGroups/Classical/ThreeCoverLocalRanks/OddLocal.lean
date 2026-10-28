module

public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.SpecificGroups.SL3.InvolutionBlock
public import Theory.GroupTheory.PrimeRankProduct
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Odd signed degree-three local witnesses

Odd-prime signed degree-three covers contain the explicit cubic diagonal and
scalar witnesses in the centralizer of the standard involution. The cyclic
involution subgroup is a genuine nontrivial two-local, and its normalizer
retains rank two. Unitarians use the original Hermitian form and an actual
orthonormal-basis transport; no even-characteristic SL₂ center assertion is
used.

Source: Aschbacher–Smith A.2.12(I), printed pp.36–37.
-/

open Matrix Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace Theory.SpecificGroups.Classical.ThreeCoverLocalRanks
open Theory.SpecificGroups.SignedThreeCubicRank
variable {F : Type*} [Field F]

private theorem exists_cubic [Finite F] (hd : 3 ∣ Nat.card F - 1) :
    ∃ u : F, u ^ 3 = 1 ∧ u ≠ 1 := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rwa [Nat.card_units])
  exact ⟨u, congrArg Units.val (orderOf_eq_prime_iff.mp hu).1,
    fun he => (orderOf_eq_prime_iff.mp hu).2 (Units.ext he)⟩

private theorem local_witness_of_centralizer_rank {G : Type*} [Group G] [Finite G]
    (t : G) (ht : orderOf t = 2) (hr : 2 ≤ primeRank 3 (centralizer {t})) :
    ∃ R : Subgroup G, R ≠ ⊥ ∧ IsPGroup 2 R ∧ 2 ≤ primeRank 3 (normalizer (R : Set G)) := by
  have hle : centralizer ({t} : Set G) ≤ normalizer (zpowers t : Set G) := by
    intro x hx
    apply centralizer_le_normalizer
    intro y hy
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    exact ((show Commute t x from (mem_centralizer_singleton_iff.mp hx).symm).zpow_left n).eq
  refine ⟨zpowers t, ?_, IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, ht]), ?_⟩
  · intro h
    have h1 : t = 1 := mem_bot.mp (h ▸ mem_zpowers t)
    simp [h1] at ht
  · exact hr.trans (primeRank_le_of_injective 3 (inclusion hle) (inclusion_injective hle))

private theorem diagonal_commutes_sign (u : F) (hu : u ^ 3 = 1) :
    Commute (diagonal u hu) (Matrix.SL3.standardInvolution F) := by
  apply Subtype.ext
  change (diagonal u hu).val * (Matrix.SL3.standardInvolution F).val =
    (Matrix.SL3.standardInvolution F).val * (diagonal u hu).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SignedThreeCubicRank.diagonal, Matrix.SL3.standardInvolution, Matrix.mul_apply, Fin.sum_univ_three]

private theorem scalar_commutes_sign (u : F) (hu : u ^ 3 = 1) :
    Commute (scalar u hu) (Matrix.SL3.standardInvolution F) := by
  exact ((mem_center_iff.mp (SpecialLinearGroup.mem_center_iff.mpr ⟨u, by simpa using hu, rfl⟩)) _).symm

/-- Explicit cubic rank two in the normalizer of the sign involution subgroup. -/
public theorem linear_local_cubic_witness [Finite F]
    (h2 : (2 : F) ≠ 0) (hd : 3 ∣ Nat.card F - 1) :
    ∃ R : Subgroup SL(3,F), R ≠ ⊥ ∧ IsPGroup 2 R ∧
      2 ≤ primeRank 3 (normalizer (R : Set SL(3,F))) := by
  obtain ⟨u, hu, hne⟩ := exists_cubic hd
  let t := Matrix.SL3.standardInvolution F
  let C := centralizer ({t} : Set SL(3,F))
  let x : C := ⟨diagonal u hu, mem_centralizer_singleton_iff.mpr (diagonal_commutes_sign u hu)⟩
  let y : C := ⟨scalar u hu, mem_centralizer_singleton_iff.mpr (scalar_commutes_sign u hu)⟩
  apply local_witness_of_centralizer_rank t (Matrix.SL3.standardInvolution_orderOf F h2)
  exact special_rank u hu hne (SpecialLinearGroup.toGL.comp C.subtype)
    (SpecialLinearGroup.toGL_injective.comp C.subtype_injective) x y rfl rfl

private theorem sign_unitary (J : HermitianForm 3 F) (hJ : J.form = 1) :
    SpecialLinearGroup.toGL (Matrix.SL3.standardInvolution F) ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  refine ⟨?_, SpecialLinearGroup.coeToGL_det _⟩
  rw [hJ, mul_one]
  change J.conjTranspose (Matrix.SL3.standardInvolution F).val *
    (Matrix.SL3.standardInvolution F).val = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SL3.standardInvolution, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_three]

private theorem diagonal_unitary (u : F) (hu : u ^ 3 = 1)
    (J : HermitianForm 3 F) (hJ : J.form = 1) (hnorm : J.conj u * u = 1) :
    SpecialLinearGroup.toGL (diagonal u hu) ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  refine ⟨?_, SpecialLinearGroup.coeToGL_det _⟩
  rw [hJ, mul_one]
  change J.conjTranspose (diagonal u hu).val * (diagonal u hu).val = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SignedThreeCubicRank.diagonal, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_three, hnorm]
  calc J.conj u ^ 2 * u ^ 2 = (J.conj u * u) ^ 2 := by ring
       _ = 1 := by rw [hnorm]; simp

private theorem scalar_unitary (u : F) (hu : u ^ 3 = 1)
    (J : HermitianForm 3 F) (hJ : J.form = 1) (hnorm : J.conj u * u = 1) :
    SpecialLinearGroup.toGL (scalar u hu) ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  refine ⟨?_, SpecialLinearGroup.coeToGL_det _⟩
  rw [hJ, mul_one]
  change J.conjTranspose (scalar u hu).val * (scalar u hu).val = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SignedThreeCubicRank.scalar, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_three, hnorm]

private theorem identity_unitary_local_cubic_witness [Finite F]
    (J : HermitianForm 3 F) (hJ : J.form = 1) (h2 : (2 : F) ≠ 0)
    (u : F) (hu : u ^ 3 = 1) (hne : u ≠ 1) (hnorm : J.conj u * u = 1) :
    ∃ R : Subgroup J.specialSubgroup, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      2 ≤ primeRank 3 (normalizer (R : Set J.specialSubgroup)) := by
  let t : J.specialSubgroup := ⟨SpecialLinearGroup.toGL (Matrix.SL3.standardInvolution F),
    sign_unitary J hJ⟩
  have ht : orderOf t = 2 := by
    rw [← orderOf_coe]
    change orderOf (SpecialLinearGroup.toGL (Matrix.SL3.standardInvolution F)) = 2
    rw [orderOf_injective SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective]
    exact Matrix.SL3.standardInvolution_orderOf F h2
  let C := centralizer ({t} : Set J.specialSubgroup)
  let x : C := ⟨⟨SpecialLinearGroup.toGL (diagonal u hu), diagonal_unitary u hu J hJ hnorm⟩,
    mem_centralizer_singleton_iff.mpr (by
      apply Subtype.ext
      exact (diagonal_commutes_sign u hu).map SpecialLinearGroup.toGL |>.eq)⟩
  let y : C := ⟨⟨SpecialLinearGroup.toGL (scalar u hu), scalar_unitary u hu J hJ hnorm⟩,
    mem_centralizer_singleton_iff.mpr (by
      apply Subtype.ext
      exact (scalar_commutes_sign u hu).map SpecialLinearGroup.toGL |>.eq)⟩
  apply local_witness_of_centralizer_rank t ht
  exact special_rank u hu hne (J.specialSubgroup.subtype.comp C.subtype)
    (J.specialSubgroup.subtype_injective.comp C.subtype_injective) x y rfl rfl

private theorem local_witness_transport {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B)
    (h : ∃ R : Subgroup A, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      2 ≤ primeRank 3 (normalizer (R : Set A))) :
    ∃ R : Subgroup B, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      2 ≤ primeRank 3 (normalizer (R : Set B)) := by
  obtain ⟨R, hR, hp, hr⟩ := h
  let R' := R.map e.toMonoidHom
  have hle : (normalizer (R : Set A)).map e.toMonoidHom ≤ normalizer (R' : Set B) :=
    le_normalizer_map e.toMonoidHom
  refine ⟨R', fun hh => hR ((map_eq_bot_iff_of_injective R e.injective).mp hh), hp.map _, ?_⟩
  have he : primeRank 3 (normalizer (R : Set A)) =
      primeRank 3 ((normalizer (R : Set A)).map e.toMonoidHom) :=
    primeRank_equiv 3 (equivMapOfInjective _ e.toMonoidHom e.injective)
  rw [he] at hr
  exact hr.trans (primeRank_le_of_injective 3 (inclusion hle) (inclusion_injective hle))

private theorem two_ne_zero_of_odd_prime_power [Finite F] {p n : ℕ} [Fact p.Prime]
    (hp : Odd p) (hcard : Nat.card F = p ^ n) : (2 : F) ≠ 0 := by
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow
    (by simpa only [← Nat.card_eq_fintype_card] using hcard)
  change (↑(2 : ℕ) : F) ≠ 0
  rw [ne_eq, CharP.cast_eq_zero_iff F p]
  intro hd
  have he := (Nat.dvd_prime Nat.prime_two).mp hd
  have hpl := (Fact.out : p.Prime).two_le
  have ho := Nat.odd_iff.mp hp
  omega

/-- The odd-prime linear source witness, with the actual matrix field order. -/
public theorem linear_odd_prime_local_cubic_witness [Finite F] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hcard : Nat.card F = p) (hmod : p % 3 = 1) :
    ∃ R : Subgroup SL(3,F), R ≠ ⊥ ∧ IsPGroup 2 R ∧
      2 ≤ primeRank 3 (normalizer (R : Set SL(3,F))) := by
  apply linear_local_cubic_witness
  · exact two_ne_zero_of_odd_prime_power hp (n := 1) (by simpa using hcard)
  · rw [hcard]
    have hp0 := (Fact.out : p.Prime).pos
    omega

/-- The odd-prime unitary source witness on the original Hermitian carrier. -/
public theorem unitary_odd_prime_local_cubic_witness [Finite F]
    (J : HermitianForm 3 F) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hcard : Nat.card F = p ^ 2)
    (hconj : ∀ x, J.conj x = x ^ p) (hmod : p % 3 = 2) :
    ∃ R : Subgroup J.specialSubgroup, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      2 ≤ primeRank 3 (normalizer (R : Set J.specialSubgroup)) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_prime_power hp hcard
  have hdiv : 3 ∣ Nat.card F - 1 := by
    rw [hcard]
    have hp0 := (Fact.out : p.Prime).pos
    have hm : p ^ 2 % 3 = 1 := by norm_num [Nat.pow_mod, hmod]
    have hpos : 0 < p ^ 2 := pow_pos hp0 _
    omega
  obtain ⟨u, hu, hne⟩ := exists_cubic hdiv
  have hnorm : J.conj u * u = 1 := by
    rw [hconj, ← pow_succ]
    have hd : 3 ∣ p + 1 := by omega
    obtain ⟨k, hk⟩ := hd
    rw [hk, pow_mul, hu, one_pow]
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
      (by simpa using hcard) (by simpa using hconj)
  obtain ⟨C, hC⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis 3 J p hcard hfixed
  exact local_witness_transport (HermitianForm.IdentityGram.specialEquiv J C hC).symm
    (identity_unitary_local_cubic_witness (HermitianForm.IdentityGram.identityGram J) rfl
      h2 u hu hne hnorm)
end Theory.SpecificGroups.Classical.ThreeCoverLocalRanks
