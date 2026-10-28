module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTorus
public import Theory.SpecificGroups.ClassicalUnitary.OddFourRanks.Torus
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.GroupTheory.QuasithinBasic

/-!
# Ordinary odd-prime ranks in small-dimensional unitary groups

The PSU4 determinant-one norm-one torus has three independent odd-prime
coordinates; the scalar kernel has order dividing four and kills none of
them. In PSU5 we fix the first diagonal entry to one, making a three-coordinate
torus faithful even at the prime five. Orthonormalization transports both
constructions to every nondegenerate Hermitian form with the prescribed
Frobenius involution. The field has order q^2; q is its fixed-field size.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, A.2.18,
printed p.40, the ordinary-rank exclusions for U4(q) and U5(4).
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.ClassicalUnitary.EvenSmallRanks
variable {F : Type*} [Field F]

private theorem roots_card [Finite F] {q p : ℕ} [NeZero p]
    (hcard : Nat.card F = q ^ 2) (hq : 2 ≤ q) (hd : p ∣ q + 1) :
    Nat.card (rootsOfUnity p F) = p := by
  apply FiniteField.card_rootsOfUnity_of_dvd
  rw [hcard]
  have he : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    nlinarith [Nat.sub_add_cancel (show 1 ≤ q by omega),
      Nat.sub_add_cancel (show 1 ≤ q ^ 2 by nlinarith)]
  rw [he]
  exact dvd_mul_of_dvd_left hd _

theorem four_identity_rank [Finite F] (J : HermitianForm 4 F) (hJ : J.form = 1)
    {q p : ℕ} (hcard : Nat.card F = q ^ 2) (hq : 2 ≤ q)
    (hconj : ∀ x, J.conj x = x ^ q) (hp : p.Prime) (ho : p ≠ 2)
    (hd : p ∣ q + 1) : 3 ≤ primeRank p (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨f, hf⟩ := OddFourRanks.exists_torsion_embedding J hJ hconj hp ho hd
  apply primeRank_ge_of_elementary_embedding
    (f := (Subgroup.subtype _).comp f) (hf := Subtype.val_injective.comp hf)
  · intro a
    funext i
    exact Subtype.ext ((mem_rootsOfUnity p _).mp (a i).property)
  · rw [Nat.card_fun, roots_card hcard hq hd, Nat.card_fin]

variable (J : HermitianForm 5 F) (hJ : J.form = 1)
variable (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)

def entries (a : Fin 3 → C) : Fin 5 → C :=
  ![1, a 0, a 1, a 2, (a 0 * a 1 * a 2)⁻¹]

theorem entries_det (a : Fin 3 → C) :
    (diagonal (fun i => ((entries C a i).val : F))).det = 1 := by
  rw [det_diagonal]
  simp [entries, Fin.prod_univ_succ, ← mul_assoc]

noncomputable def torusMatrix (a : Fin 3 → C) : GL (Fin 5) F :=
  GeneralLinearGroup.mkOfDetNeZero
    (diagonal (fun i => ((entries C a i).val : F)))
    (by rw [entries_det]; exact one_ne_zero)

@[simp] theorem torusMatrix_val (a : Fin 3 → C) :
    (torusMatrix C a : Matrix (Fin 5) (Fin 5) F) =
      diagonal (fun i => ((entries C a i).val : F)) := rfl

noncomputable def torusSpecial : (Fin 3 → C) →* J.specialSubgroup where
  toFun a := ⟨torusMatrix C a, by
    rw [J.mem_specialSubgroup_iff]
    constructor
    · rw [hJ, Matrix.mul_one]
      change J.conjTranspose (diagonal _) * diagonal _ = 1
      ext i j
      by_cases h : j = i <;> simp [HermitianForm.conjTranspose, Matrix.mul_apply,
        Matrix.diagonal_apply, Matrix.one_apply, h, Ne.symm, hC]
    · apply Units.ext
      simpa only [GeneralLinearGroup.val_det_apply, Units.val_one, torusMatrix_val] using
        entries_det C a⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [torusMatrix, entries]
  map_mul' a b := by
    apply Subtype.ext
    apply Units.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [entries, mul_assoc, mul_comm, mul_left_comm]

noncomputable def torusProjective : (Fin 3 → C) →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (UnitaryFive.project J).comp (torusSpecial J hJ C hC)

theorem torusProjective_injective : Function.Injective (torusProjective J hJ C hC) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hp : ProjGenLinGroup.mk (torusMatrix C a) = 1 := congrArg Subtype.val ha
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
  obtain ⟨u, hu⟩ := hp
  have hd (i : Fin 5) : ((entries C a i).val : F) = (u : F) := by
    have hi := congrArg (fun g : GL (Fin 5) F => g.val i i) hu
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar, torusMatrix] using hi.symm
  have hu1 : (u : F) = 1 := (hd 0).symm
  funext i
  apply Subtype.ext
  apply Units.ext
  fin_cases i
  · exact (hd 1).trans hu1
  · exact (hd 2).trans hu1
  · exact (hd 3).trans hu1

include hJ in
theorem five_identity_rank [Finite F] {q p : ℕ}
    (hcard : Nat.card F = q ^ 2) (hq : 2 ≤ q)
    (hconj : ∀ x, J.conj x = x ^ q) (hp : p.Prime) (hd : p ∣ q + 1) :
    3 ≤ primeRank p (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Finite (GL (Fin 5) F) := Finite.of_injective Units.val Units.val_injective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective (UnitaryFive.project J) (UnitaryFive.project_surjective J)
  have hn (u : rootsOfUnity p F) : J.conj (u.val : F) * (u.val : F) = 1 := by
    rw [hconj, ← pow_succ]
    obtain ⟨d, hd⟩ := hd
    rw [hd, pow_mul, (mem_rootsOfUnity' p u.val).mp u.property, one_pow]
  apply primeRank_ge_of_elementary_embedding
    (f := torusProjective J hJ (rootsOfUnity p F) hn)
    (hf := torusProjective_injective J hJ (rootsOfUnity p F) hn)
  · intro a
    funext i
    exact Subtype.ext ((mem_rootsOfUnity p _).mp (a i).property)
  · rw [Nat.card_fun, roots_card hcard hq hd, Nat.card_fin]

private theorem fixed_card [Finite F] {d q : ℕ} (J : HermitianForm d F)
    (hq : IsPrimePow q) (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) : Nat.card {x : F // J.conj x = x} = q := by
  obtain ⟨p, n, hp, hn, rfl⟩ := (isPrimePow_nat_iff q).mp hq
  let : Fact p.Prime := ⟨hp⟩
  exact FiniteField.card_fixed_of_quadratic_frobenius J.conj p n hn hcard hconj

omit J hJ C hC in
theorem four_rank [Finite F] (J : HermitianForm 4 F) {q p : ℕ}
    (hq : IsPrimePow q) (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) (hp : p.Prime) (ho : p ≠ 2)
    (hd : p ∣ q + 1) : 3 ≤ primeRank p (ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨P, hP⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    4 J q hcard (fixed_card J hq hcard hconj)
  rw [Theory.GroupTheory.primeRank_equiv p (HermitianForm.IdentityGram.projectiveEquiv J P hP)]
  exact four_identity_rank (HermitianForm.IdentityGram.identityGram J) rfl
    hcard hq.one_lt hconj hp ho hd

theorem five_rank [Finite F] {q p : ℕ}
    (hq : IsPrimePow q) (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) (hp : p.Prime) (hd : p ∣ q + 1) :
    3 ≤ primeRank p (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (GL (Fin 5) F) := Finite.of_injective Units.val Units.val_injective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective (UnitaryFive.project J) (UnitaryFive.project_surjective J)
  obtain ⟨P, hP⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    5 J q hcard (fixed_card J hq hcard hconj)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup (HermitianForm.IdentityGram.identityGram J)) :=
    Finite.of_injective (HermitianForm.IdentityGram.projectiveEquiv J P hP).symm
      (HermitianForm.IdentityGram.projectiveEquiv J P hP).symm.injective
  rw [Theory.GroupTheory.primeRank_equiv p (HermitianForm.IdentityGram.projectiveEquiv J P hP)]
  exact five_identity_rank (HermitianForm.IdentityGram.identityGram J) rfl
    hcard hq.one_lt hconj hp hd
end Theory.SpecificGroups.ClassicalUnitary.EvenSmallRanks
