module

public import Theory.SpecificGroups.SU3.BorelTorus.Basic
import Mathlib.Data.Int.GCD

/-!
# Removing diagonal factors from triangular unitary actors

For the antidiagonal Hermitian form, an upper triangular unitary matrix
factors as a genuine special-unitary root matrix times a diagonal unitary
matrix. Each diagonal entry is a field unit, so the diagonal factor has
order dividing `|E| - 1`.

For either SU₃ or its actual projective image, remove the root inner actor
inside the given two-subgroup of automorphisms. The remaining actor is
conjugation by the diagonal factor and hence has order dividing `|E| - 1`.
When `|E| = (2^n)^2`, coprimality forces this actor to be the identity.
This argument applies to arbitrary two-power actors. It does not require
a prescribed power formula for the Hermitian involution.

Source: the unitary calculation in Aschbacher–Smith, proof of 13.8.20,
printed p.954 (PDF p.971), using Huppert II.10.12 and GLS3 Section 2.7.
-/

public section

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.SemilinearActors
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

private def diagonalGL (t : Fin 3 → Eˣ) : GL (Fin 3) E where
  val := Matrix.diagonal (fun i => (t i : E))
  inv := Matrix.diagonal (fun i => ((t i)⁻¹ : Eˣ))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp

private theorem diagonalGL_pow [Finite E] (t : Fin 3 → Eˣ) :
    diagonalGL t ^ (Nat.card E - 1) = 1 := by
  apply Units.ext
  change (Matrix.diagonal (fun i => (t i : E))) ^ (Nat.card E - 1) = 1
  rw [Matrix.diagonal_pow]
  change Matrix.diagonal (fun i => (t i : E) ^ (Nat.card E - 1)) = 1
  have h : (fun i => (t i : E) ^ (Nat.card E - 1)) = fun _ => 1 := by
    funext i
    have he := congrArg Units.val (pow_card_eq_one' (x := t i))
    simpa only [Nat.card_units, Units.val_pow_eq_pow_val, Units.val_one] using he
  rw [h]
  exact Matrix.diagonal_one

private theorem root_of_upper_unitary
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (v : J.unitarySubgroup)
    (h10 : v.val.val 1 0 = 0) (h20 : v.val.val 2 0 = 0)
    (h21 : v.val.val 2 1 = 0) (hd : ∀ i, v.val.val i i = 1) :
    ∃ z : hermitianUnipotentCoord J, v.val = hermitianUnipotentGL J z := by
  have hu := (J.mem_unitarySubgroup_iff _).mp v.property
  rw [hJ] at hu
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 2) hu
  have h22 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 2) hu
  simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
    h21, hd] at h12 h22
  have hv12 : v.val.val 1 2 = -J.conj (v.val.val 0 1) := by
    linear_combination h12
  let z : hermitianUnipotentCoord J := ⟨(v.val.val 0 1, v.val.val 0 2), by
    dsimp only
    rw [hv12, map_neg, J.conj_involutive] at h22
    linear_combination h22⟩
  refine ⟨z, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianUnipotentMatrix, z, h10, h20, h21, hd, hv12]

/-- An upper triangular unitary matrix is a root matrix times a diagonal
unitary matrix, and the diagonal factor has order dividing `|E| - 1`. -/
theorem upper_unitary_factorization [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (u : J.unitarySubgroup)
    (h10 : u.val.val 1 0 = 0) (h20 : u.val.val 2 0 = 0)
    (h21 : u.val.val 2 1 = 0) :
    ∃ z : hermitianUnipotentCoord J, ∃ d : J.unitarySubgroup,
      u.val = hermitianUnipotentGL J z * d.val ∧
      (∀ i j, i ≠ j → d.val.val i j = 0) ∧ d ^ (Nat.card E - 1) = 1 := by
  have hu := (J.mem_unitarySubgroup_iff _).mp u.property
  rw [hJ] at hu
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 2) hu
  have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 1) hu
  have h20' := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 0) hu
  simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
    h10, h20, h21] at h02 h11 h20'
  have hnz : ∀ i, u.val.val i i ≠ 0 := by
    intro i
    fin_cases i
    · exact right_ne_zero_of_mul_eq_one h20'
    · exact right_ne_zero_of_mul_eq_one h11
    · exact right_ne_zero_of_mul_eq_one h02
  let t : Fin 3 → Eˣ := fun i => Units.mk0 (u.val.val i i) (hnz i)
  have hdu : diagonalGL t ∈ J.unitarySubgroup := by
    rw [J.mem_unitarySubgroup_iff, hJ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonalGL, t, HermitianForm.conjTranspose, Matrix.mul_apply,
        Fin.sum_univ_three, h02, h11, h20']
  let d : J.unitarySubgroup := ⟨diagonalGL t, hdu⟩
  let v := u * d⁻¹
  have hv (i j : Fin 3) : v.val.val i j = u.val.val i j / u.val.val j j := by
    change (u.val.val * Matrix.diagonal (fun j => (((t j)⁻¹ : Eˣ) : E))) i j = _
    rw [Matrix.mul_diagonal]
    simp [t, div_eq_mul_inv]
  obtain ⟨z, hz⟩ := root_of_upper_unitary J hJ v
    (by simp [hv, h10]) (by simp [hv, h20]) (by simp [hv, h21])
    (fun i => by simp [hv, hnz])
  refine ⟨z, d, ?_, ?_, ?_⟩
  · rw [← hz]
    change u.val = u.val * d.val⁻¹ * d.val
    group
  · intro i j hij
    exact Matrix.diagonal_apply_ne _ hij
  · apply Subtype.ext
    exact diagonalGL_pow t

private theorem actor_pow_eq_one {D G : Type*} [Group D] [Group G]
    (f : D →* G) (hf : Function.Injective f) (a : MulAut D) (d : G)
    (ha : ∀ x, f (a x) = d * f x * d⁻¹)
    {m : ℕ} (hd : d ^ m = 1) : a ^ m = 1 := by
  have hp (k : ℕ) (x : D) : f ((a ^ k) x) = d ^ k * f x * (d ^ k)⁻¹ := by
    induction k generalizing x with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, MulAut.mul_apply, ih, ha, pow_succ]
      group
  apply MulEquiv.ext
  intro x
  apply hf
  simpa only [MulAut.one_apply, hd, one_mul, inv_one, mul_one] using hp m x

private theorem mem_inner_image_of_odd_complement {D G : Type*} [Group D] [Group G]
    (f : D →* G) (hf : Function.Injective f) (R : Subgroup D)
    (A : Subgroup (MulAut D)) (hA : IsPGroup 2 A)
    (hRA : R.map MulAut.conj ≤ A) (a : MulAut D) (ha : a ∈ A)
    (r : D) (hr : r ∈ R) (d : G) {m : ℕ} (hm : Nat.Coprime 2 m)
    (hd : d ^ m = 1)
    (hformula : ∀ x, f (a x) = (f r * d) * f x * (f r * d)⁻¹) :
    a ∈ R.map MulAut.conj := by
  have hc : MulAut.conj r ∈ R.map MulAut.conj := ⟨r, hr, rfl⟩
  let b := (MulAut.conj r)⁻¹ * a
  have hbA : b ∈ A := A.mul_mem (A.inv_mem (hRA hc)) ha
  have hbf (x : D) : f (b x) = d * f x * d⁻¹ := by
    change f (((MulAut.conj r)⁻¹) (a x)) = _
    rw [← map_inv, MulAut.conj_apply]
    simp only [map_mul, map_inv, hformula]
    group
  have hbm : b ^ m = 1 := actor_pow_eq_one f hf b d hbf hd
  obtain ⟨k, hk⟩ := hA ⟨b, hbA⟩
  have hb2 : b ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hb1 : b = 1 := (pow_eq_one_iff_of_coprime (hm.pow_left k)).mp ⟨hb2, hbm⟩
  have hae : a = MulAut.conj r := (inv_mul_eq_one.mp hb1).symm
  exact hae ▸ hc

omit [Field E] in
private theorem card_sub_one_coprime_two {n : ℕ}
    (hcard : Nat.card E = (2 ^ n) ^ 2) (hn : 0 < n) :
    Nat.Coprime 2 (Nat.card E - 1) := by
  apply Nat.coprime_two_left.mpr
  rw [hcard]
  have he : Even ((2 ^ n) ^ 2) := (even_two.pow_of_ne_zero (by omega)).pow_of_ne_zero (by decide)
  have hpos : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  exact Nat.Even.sub_odd hpos he odd_one

/-- In SU₃, a two-power actor in a two-subgroup containing the root inner
image, represented by conjugation with an upper triangular unitary matrix,
is already a root inner automorphism. -/
theorem special_identity_field_mem_root_inner [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hcard : Nat.card E = (2 ^ n) ^ 2) (hn : 1 < n)
    (A : Subgroup (MulAut J.specialSubgroup)) (hA : IsPGroup 2 A)
    (hUA : (specialRoot J hJ).map MulAut.conj ≤ A)
    (a : MulAut J.specialSubgroup) (ha : a ∈ A) (u : J.unitarySubgroup)
    (h10 : u.val.val 1 0 = 0) (h20 : u.val.val 2 0 = 0)
    (h21 : u.val.val 2 1 = 0)
    (hu : ∀ x : J.specialSubgroup, (a x).val = u.val * x.val * u.val⁻¹) :
    a ∈ (specialRoot J hJ).map MulAut.conj := by
  obtain ⟨z, d, hfactor, _, hd⟩ := upper_unitary_factorization J hJ u h10 h20 h21
  apply mem_inner_image_of_odd_complement J.specialSubgroup.subtype Subtype.val_injective
    (specialRoot J hJ) A hA hUA a ha (hermitianUnipotentSU J hJ z) ⟨z, rfl⟩ d.val
    (card_sub_one_coprime_two hcard (by omega)) (congrArg Subtype.val hd)
  intro x
  change (a x).val = (hermitianUnipotentGL J z * d.val) * x.val *
    (hermitianUnipotentGL J z * d.val)⁻¹
  simpa only [hfactor] using hu x

/-- The same calculation in the actual PSU₃ carrier, retaining the PGL
conjugation formula rather than choosing representatives of projective elements. -/
theorem projective_identity_field_mem_root_inner [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hcard : Nat.card E = (2 ^ n) ^ 2) (hn : 1 < n)
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (hA : IsPGroup 2 A)
    (hUA : (projectiveRoot J hJ).map MulAut.conj ≤ A)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ∈ A)
    (u : J.unitarySubgroup)
    (h10 : u.val.val 1 0 = 0) (h20 : u.val.val 2 0 = 0)
    (h21 : u.val.val 2 1 = 0)
    (hu : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      (a x).val = ProjGenLinGroup.mk u.val * x.val * (ProjGenLinGroup.mk u.val)⁻¹) :
    a ∈ (projectiveRoot J hJ).map MulAut.conj := by
  obtain ⟨z, d, hfactor, _, hd⟩ := upper_unitary_factorization J hJ u h10 h20 h21
  have hdp : (ProjGenLinGroup.mk d.val) ^ (Nat.card E - 1) = 1 := by
    have he := congrArg ProjGenLinGroup.mk (congrArg Subtype.val hd)
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] using he
  apply mem_inner_image_of_odd_complement (ProjectiveSpecialUnitaryMatrixGroup J).subtype
    Subtype.val_injective (projectiveRoot J hJ) A hA hUA a ha
    (hermitianUnipotentPSU J hJ z) ⟨z, rfl⟩ (ProjGenLinGroup.mk d.val)
    (card_sub_one_coprime_two hcard (by omega)) hdp
  intro x
  change (a x).val = (ProjGenLinGroup.mk (hermitianUnipotentGL J z) *
    ProjGenLinGroup.mk d.val) * x.val *
    (ProjGenLinGroup.mk (hermitianUnipotentGL J z) * ProjGenLinGroup.mk d.val)⁻¹
  simpa only [hfactor, map_mul] using hu x

end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.SemilinearActors
