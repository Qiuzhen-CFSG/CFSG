module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Contracts

/-!
# The scalar centralizer of the binary Hermitian tensor

Every binary endomorphism commuting with the literal SL₃ action is
multiplication by an element of the actual fixed field. Invertibility then
makes that coefficient a unit, giving `ScalarCentralizerCoverage` with the
published `fixedScalar` map.

The proof starts with the matrix E₀₀. Elementary matrices fixing its first
column have common fixed space F E₀₀, so a commuting endomorphism sends
E₀₀ to a scalar multiple of itself. Every nonzero column extends to a
matrix of determinant one, so the same scalar acts on all matrices v σ(v)ᵀ.
These generate the Hermitian space additively: fixed-field coefficients
have square roots, and off-diagonal Hermitian pairs are differences of
three such matrices. No irreducibility or commutant hypothesis is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.4.2
setup, printed p.380 (with the standing binary-module convention on p.377).
This supplies the scalar-centralizer input to the normalizer assembly;
the independent induced-action input remains separate.
-/

public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter.Centralizer
variable (n : ℕ) [NeZero n]

private def seed : Space n :=
  ⟨Matrix.single 0 0 1, by ext i j; simp [adjoint, Matrix.single_apply]⟩

private theorem seed_action (g : Cover n) (i j : Fin 3) :
    (binaryActionHom n g (seed n)).val i j = g.val i 0 * sigma n (g.val j 0) := by
  change (g.val * (seed n).val * adjoint n g.val) i j = _
  simp [seed, Matrix.mul_apply, Matrix.single_apply, adjoint, ite_and]

omit [NeZero n] in
private theorem adjoint_transvection (i j : Fin 3) :
    adjoint n (Matrix.transvection i j (1 : E n)) = Matrix.transvection j i 1 := by
  ext a b
  simp [adjoint, Matrix.transvection, Matrix.one_apply, Matrix.single_apply]

private theorem fixed_entry (X : Space n) (i j k : Fin 3) (hij : i ≠ j) (hki : k ≠ i)
    (h : binaryActionHom n (Matrix.SpecialLinearGroup.transvection hij (1 : E n)) X = X) :
    X.val j k = 0 := by
  have he := congrArg (fun Y : Space n => Y.val i k) h
  change (((Matrix.transvection i j (1 : E n)) * X.val *
    adjoint n (Matrix.transvection i j (1 : E n))) i k) = X.val i k at he
  rw [adjoint_transvection, Matrix.mul_transvection_apply_of_ne _ _ _ _ hki,
    Matrix.transvection_mul_apply_same, one_mul] at he
  exact add_eq_left.mp he

private theorem transvection_fixes_seed (i j : Fin 3) (hij : i ≠ j) (hj : j ≠ 0) :
    binaryActionHom n (Matrix.SpecialLinearGroup.transvection hij (1 : E n)) (seed n) =
      seed n := by
  apply Subtype.ext
  ext a b
  rw [seed_action]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, seed,
      hj, ha, hb, eq_comm]

private theorem fixed_seed_line (Y : Space n)
    (h : ∀ (i j : Fin 3) (hij : i ≠ j), j ≠ 0 →
      binaryActionHom n (Matrix.SpecialLinearGroup.transvection hij (1 : E n)) Y = Y) :
    ∃ c : F n, Y = c • seed n := by
  have h11 := fixed_entry n Y 0 1 1 (by decide) (by decide) (h 0 1 (by decide) (by decide))
  have h12 := fixed_entry n Y 0 1 2 (by decide) (by decide) (h 0 1 (by decide) (by decide))
  have h22 := fixed_entry n Y 0 2 2 (by decide) (by decide) (h 0 2 (by decide) (by decide))
  have h10 := fixed_entry n Y 2 1 0 (by decide) (by decide) (h 2 1 (by decide) (by decide))
  have h20 := fixed_entry n Y 1 2 0 (by decide) (by decide) (h 1 2 (by decide) (by decide))
  have h01 : Y.val 0 1 = 0 := by rw [← entry_conjugate n Y 0 1, h10, map_zero]
  have h02 : Y.val 0 2 = 0 := by rw [← entry_conjugate n Y 0 2, h20, map_zero]
  have h21 : Y.val 2 1 = 0 := by rw [← entry_conjugate n Y 2 1, h12, map_zero]
  refine ⟨⟨Y.val 0 0, entry_conjugate n Y 0 0⟩, ?_⟩
  apply Subtype.ext
  ext i j
  change Y.val i j = Y.val 0 0 * (Matrix.single 0 0 (1 : E n)) i j
  fin_cases i <;> fin_cases j <;>
    simp [h11, h12, h22, h10, h20, h01, h02, h21]

private def rankOne (v : Natural n) : Space n :=
  ⟨fun i j => v i * sigma n (v j), by
    ext i j
    change sigma n (v j * sigma n (v i)) = v i * sigma n (v j)
    rw [map_mul, sigma_involutive, mul_comm]⟩

omit [NeZero n] in
private theorem exists_first_column (v : Natural n) (hv : v ≠ 0) :
    ∃ g : Cover n, ∀ i, g.val i 0 = v i := by
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · have h2 : v 2 ≠ 0 := by
        intro h2
        apply hv
        ext i
        fin_cases i <;> simp [h0, h1, h2]
      refine ⟨⟨!![v 0,0,-(v 2)⁻¹;v 1,1,0;v 2,0,0], ?_⟩, ?_⟩
      · simp [Matrix.det_fin_three, h2]
      · intro i; fin_cases i <;> rfl
    · refine ⟨⟨!![v 0,-(v 1)⁻¹,0;v 1,0,0;v 2,0,1], ?_⟩, ?_⟩
      · simp [Matrix.det_fin_three, h1]
      · intro i; fin_cases i <;> rfl
  · refine ⟨⟨!![v 0,0,0;v 1,(v 0)⁻¹,0;v 2,0,1], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_three, h0]
    · intro i; fin_cases i <;> rfl

private theorem rankOne_is_orbit (v : Natural n) (hv : v ≠ 0) :
    ∃ g : Cover n, binaryActionHom n g (seed n) = rankOne n v := by
  obtain ⟨g, hg⟩ := exists_first_column n v hv
  refine ⟨g, ?_⟩
  apply Subtype.ext
  ext i j
  rw [seed_action, hg, hg]
  rfl

private def diagonalAt (i : Fin 3) (c : F n) : Space n :=
  ⟨Matrix.single i i c.val, by
    have hc : sigma n c.val = c.val := c.property
    ext a b
    simp only [adjoint, Matrix.map_apply, Matrix.transpose_apply, Matrix.single_apply, and_comm]
    split_ifs <;> simp only [hc, map_zero]⟩

private theorem diagonalAt_is_rankOne (i : Fin 3) (c : F n) :
    ∃ v : Natural n, diagonalAt n i c = rankOne n v := by
  obtain ⟨d, hd⟩ := surjective_frobenius (F n) 2 c
  have hd2 : d ^ 2 = c := hd
  have hdE : (d.val : E n) * d.val = c.val := by
    exact congrArg Subtype.val (by simpa only [pow_two] using hd2)
  refine ⟨Pi.single i d.val, ?_⟩
  apply Subtype.ext
  ext a b
  change (Matrix.single i i c.val) a b =
    (Pi.single i d.val : Natural n) a * sigma n ((Pi.single i d.val : Natural n) b)
  have hdσ : sigma n d.val = d.val := d.property
  by_cases ha : a = i
  · subst a
    by_cases hb : b = i
    · subst b; simp [hdσ, hdE]
    · simp [hb, Ne.symm hb]
  · simp [ha, Ne.symm ha]

private def offDiagonal (i j : Fin 3) (a : E n) : Space n :=
  ⟨Matrix.single i j a + Matrix.single j i (sigma n a), by
    ext k l
    simp only [adjoint, Matrix.map_apply, Matrix.transpose_apply, Matrix.add_apply,
      Matrix.single_apply, map_add, @and_comm (i = l) (j = k), @and_comm (j = l) (i = k)]
    split_ifs <;> simp only [map_zero, sigma_involutive n a, add_zero, zero_add, add_comm]⟩

private theorem offDiagonal_eq (i j : Fin 3) (a : E n) :
    offDiagonal n i j a =
      rankOne n (Pi.single i 1 + Pi.single j (sigma n a)) -
        rankOne n (Pi.single i 1) - rankOne n (Pi.single j (sigma n a)) := by
  apply Subtype.ext
  ext k l
  let u : Natural n := Pi.single i 1
  let v : Natural n := Pi.single j (sigma n a)
  change (Matrix.single i j a) k l + (Matrix.single j i (sigma n a)) k l =
    (u k + v k) * sigma n (u l + v l) - u k * sigma n (u l) - v k * sigma n (v l)
  simp only [u, v, Matrix.single_apply, Pi.single_apply]
  simp_rw [@eq_comm _ i k, @eq_comm _ j l, @eq_comm _ j k, @eq_comm _ i l]
  split_ifs <;> (try omega) <;>
    simp only [map_add, map_zero, map_one, sigma_involutive n a] <;> ring

private theorem decomposition (X : Space n) :
    X = diagonalAt n 0 ⟨X.val 0 0, entry_conjugate n X 0 0⟩ +
      diagonalAt n 1 ⟨X.val 1 1, entry_conjugate n X 1 1⟩ +
      diagonalAt n 2 ⟨X.val 2 2, entry_conjugate n X 2 2⟩ +
      offDiagonal n 0 1 (X.val 0 1) + offDiagonal n 0 2 (X.val 0 2) +
      offDiagonal n 1 2 (X.val 1 2) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalAt, offDiagonal, entry_conjugate]

end Representation.HermitianTensorThree.ImageOuter.Centralizer

namespace Representation.HermitianTensorThree.ImageOuter
open Centralizer
variable (n : ℕ) [NeZero n]

/-- Every binary endomorphism commuting with the actual SL₃ action is a fixed-field scalar. -/
theorem binaryEndomorphism_eq_smul (f : Space n →ₗ[ZMod 2] Space n)
    (hf : ∀ (a : Cover n) (X : Space n),
      f (binaryActionHom n a X) = binaryActionHom n a (f X)) :
    ∃ c : F n, ∀ X : Space n, f X = c • X := by
  obtain ⟨c, hc⟩ := fixed_seed_line n (f (seed n)) (by
    intro i j hij hj
    rw [← hf, transvection_fixes_seed n i j hij hj])
  have h_rank (v : Natural n) : f (rankOne n v) = c • rankOne n v := by
    by_cases hv : v = 0
    · have hz : rankOne n v = 0 := by
        apply Subtype.ext
        ext i j
        simp [rankOne, hv]
      simp [hz]
    · obtain ⟨g, hg⟩ := rankOne_is_orbit n v hv
      rw [← hg, hf, hc]
      exact (actionHom n g).map_smul c (seed n)
  have h_diag (i : Fin 3) (d : F n) :
      f (diagonalAt n i d) = c • diagonalAt n i d := by
    obtain ⟨v, hv⟩ := diagonalAt_is_rankOne n i d
    rw [hv]
    exact h_rank v
  have h_off (i j : Fin 3) (a : E n) :
      f (offDiagonal n i j a) = c • offDiagonal n i j a := by
    rw [offDiagonal_eq]
    simp only [map_sub, h_rank, smul_sub]
  refine ⟨c, ?_⟩
  intro X
  conv_lhs => rw [decomposition n X]
  conv_rhs => rw [decomposition n X]
  simp only [map_add, h_diag, h_off, smul_add]

/-- The exact invertible scalar-centralizer contract for the binary Hermitian action. -/
theorem scalarCentralizerCoverage : ScalarCentralizerCoverage n := by
  intro e he
  obtain ⟨c, hc⟩ := binaryEndomorphism_eq_smul n e.toLinearMap (by
    intro a X
    exact congrArg (fun k : Space n ≃ₗ[ZMod 2] Space n => k X) (he a))
  have hc0 : c ≠ 0 := by
    intro hc0
    have hz : seed n = 0 := e.injective (by simpa [hc0] using hc (seed n))
    have hentry := congrArg (fun X : Space n => X.val 0 0) hz
    exact one_ne_zero hentry
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply LinearEquiv.ext
  intro X
  exact hc X

end Representation.HermitianTensorThree.ImageOuter
