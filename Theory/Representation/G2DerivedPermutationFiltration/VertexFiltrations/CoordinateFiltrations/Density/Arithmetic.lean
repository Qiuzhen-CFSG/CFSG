module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.Data
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
import Mathlib.Tactic

/-!
# Sound arithmetic for the diagonal-factor density certificates

Packed binary sums are interpreted as linear combinations of matrices. A
well-founded recurrence in the two generators places each stored matrix in
any subalgebra containing them; checked expressions for the matrix units then
force that subalgebra to be the whole algebra. A separate conjugation lemma
transfers density along an explicitly invertible intertwiner.

The binary arithmetic reuses the general checker in
`Thompson.Model.GeneratorCertificates.BinaryMatrix`. The present certificates
support the representation calculation in Aschbacher–Smith G.7.2(3), p.348.
-/

@[expose] public section

open scoped BigOperators
namespace G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.Density
open Thompson.BinaryMatrix

def packedMatrix (n a : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => Thompson.BinaryMatrix.bit a (n * i.val + j.val)

theorem decode_rows (n : ℕ) (a : Array ℕ) (p : ℕ)
    (h : ∀ i : Fin n, a[i.val]! = (p >>> (n * i.val)) % 2 ^ n) :
    decode n a = packedMatrix n p := by
  ext i j
  change Thompson.BinaryMatrix.bit a[i.val]! j.val =
    Thompson.BinaryMatrix.bit p (n * i.val + j.val)
  rw [h i]
  simp [Thompson.BinaryMatrix.bit, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, j.isLt]

theorem packedMatrix_combination (n m a : ℕ) (p : Array ℕ) :
    packedMatrix n (rowProduct a p m) =
      ∑ k : Fin m, Thompson.BinaryMatrix.bit a k.val • packedMatrix n p[k.val]! := by
  ext i j
  simp only [packedMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [bit_rowProduct, Fin.sum_univ_eq_sum_range (fun k =>
    Thompson.BinaryMatrix.bit a k * Thompson.BinaryMatrix.bit p[k]! (n * i.val + j.val))]

theorem packedMatrix_single (n : ℕ) (i j : Fin n) :
    packedMatrix n (2 ^ (n * i.val + j.val)) = Matrix.single i j 1 := by
  ext r s
  have he : n * i.val + j.val = n * r.val + s.val ↔ i = r ∧ j = s := by
    constructor
    · intro h
      have h₁ := congrArg (· % n) h
      have h₂ := congrArg (· / n) h
      simp only [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (Fin.isLt _)] at h₁
      have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
      simp only [Nat.mul_add_div hn, Nat.div_eq_of_lt (Fin.isLt _), Nat.add_zero] at h₂
      exact ⟨Fin.ext h₂, Fin.ext h₁⟩
    · rintro ⟨rfl, rfl⟩; rfl
  simp only [packedMatrix, Thompson.BinaryMatrix.bit, Nat.testBit_two_pow,
    decide_eq_true_eq, he, Matrix.single_apply]

theorem density_of_certificate {n m : ℕ} (A : Fin 2 → Matrix (Fin n) (Fin n) (ZMod 2))
    (p : Array ℕ) (parent : Fin m → Fin m) (letter : Fin m → Fin 2)
    (hzero : ∀ k : Fin m, k.val = 0 → packedMatrix n p[k.val]! = 1)
    (hparent : ∀ k : Fin m, k.val ≠ 0 → (parent k).val < k.val)
    (hstep : ∀ k : Fin m, k.val ≠ 0 →
      packedMatrix n p[k.val]! = A (letter k) * packedMatrix n p[(parent k).val]!)
    (coeff : Fin n → Fin n → ℕ)
    (hinverse : ∀ i j, rowProduct (coeff i j) p m = 2 ^ (n * i.val + j.val))
    (Q : Subalgebra (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)))
    (h : ∀ j, A j ∈ Q) : Q = ⊤ := by
  have hmem (k : Fin m) : packedMatrix n p[k.val]! ∈ Q := by
    induction k using Fin.strong_induction_on with
    | h k ih =>
      by_cases hk : k.val = 0
      · rw [hzero k hk]; exact Q.one_mem
      · rw [hstep k hk]
        exact Q.mul_mem (h _) (ih _ (hparent k hk))
  have hunit (i j : Fin n) : Matrix.single i j (1 : ZMod 2) ∈ Q := by
    rw [← packedMatrix_single, ← hinverse i j, packedMatrix_combination]
    exact Q.sum_mem (fun k _ => Q.smul_mem (hmem k) _)
  apply top_unique
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  exact Q.sum_mem (fun i _ => Q.sum_mem (fun j _ => by
    simpa using Q.smul_mem (hunit i j) (M i j)))

theorem density_of_intertwiner {n : ℕ}
    (A B : Fin 2 → Matrix (Fin n) (Fin n) (ZMod 2))
    (X Y : Matrix (Fin n) (Fin n) (ZMod 2)) (hXY : X * Y = 1) (hYX : Y * X = 1)
    (hinter : ∀ j, B j * X = X * A j)
    (hdense : ∀ Q : Subalgebra (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)),
      (∀ j, A j ∈ Q) → Q = ⊤)
    (Q : Subalgebra (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)))
    (h : ∀ j, B j ∈ Q) : Q = ⊤ := by
  let f : Matrix (Fin n) (Fin n) (ZMod 2) →ₐ[ZMod 2]
      Matrix (Fin n) (Fin n) (ZMod 2) :=
    { toFun := fun M => X * M * Y
      map_one' := by simpa using hXY
      map_mul' := by
        intro M N
        calc
          X * (M * N) * Y = X * M * (Y * X) * N * Y := by rw [hYX]; simp [mul_assoc]
          _ = (X * M * Y) * (X * N * Y) := by simp only [mul_assoc]
      map_zero' := by simp
      map_add' := by intro M N; simp only [mul_add, add_mul]
      commutes' := by
        intro r
        rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, hXY] }
  have hc : Q.comap f = ⊤ := hdense _ (fun j => by
    change X * A j * Y ∈ Q
    rw [← hinter, mul_assoc, hXY, mul_one]
    exact h j)
  apply top_unique
  intro M _
  have hm : Y * M * X ∈ Q.comap f := by rw [hc]; trivial
  change X * (Y * M * X) * Y ∈ Q at hm
  have hf : X * (Y * M * X) * Y = M := by
    calc
      X * (Y * M * X) * Y = (X * Y) * M * (X * Y) := by simp only [mul_assoc]
      _ = M := by rw [hXY]; simp
  rwa [hf] at hm

theorem decode_mul_eq {n : ℕ} (a b c d : Array ℕ)
    (h : ∀ i : Fin n, rowProduct a[i.val]! b n = rowProduct c[i.val]! d n) :
    decode n a * decode n b = decode n c * decode n d := by
  ext i j
  change (∑ k : Fin n, Thompson.BinaryMatrix.bit a[i.val]! k.val *
    Thompson.BinaryMatrix.bit b[k.val]! j.val) =
    ∑ k : Fin n, Thompson.BinaryMatrix.bit c[i.val]! k.val *
      Thompson.BinaryMatrix.bit d[k.val]! j.val
  rw [Fin.sum_univ_eq_sum_range (fun k => Thompson.BinaryMatrix.bit a[i.val]! k *
    Thompson.BinaryMatrix.bit b[k]! j.val),
    Fin.sum_univ_eq_sum_range (fun k => Thompson.BinaryMatrix.bit c[i.val]! k *
      Thompson.BinaryMatrix.bit d[k]! j.val), ← bit_rowProduct, ← bit_rowProduct, h i]

end G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.Density
