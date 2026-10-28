module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!
# Packed arithmetic and a rank-one density criterion

A checked straight-line program puts a rank-one matrix in the actor algebra.
Spanning translates of its column and row give every outer product; explicit
left and right inverses recover every matrix. Pullback along coefficient
casting then proves density over any field of characteristic two.
This narrow checker is used by the native PSL₃(3) incidence-cycle quotient.
-/

@[expose] public section

open scoped BigOperators Matrix
open Thompson.BinaryMatrix
namespace CycleCertificate

def rectangular (m n : ℕ) (a : Array ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bit a[i.val]! j.val

theorem rectangular_mul (m n k : ℕ) (a b c : Array ℕ)
    (h : ∀ i : Fin m, rowProduct a[i.val]! b n = c[i.val]!) :
    rectangular m n a * rectangular n k b = rectangular m k c := by
  ext i j
  change (∑ t : Fin n, bit a[i.val]! t.val * bit b[t.val]! j.val) = bit c[i.val]! j.val
  rw [Fin.sum_univ_eq_sum_range (fun t => bit a[i.val]! t * bit b[t]! j.val),
    ← bit_rowProduct, h i]

theorem decode_add (n : ℕ) (a b c : Array ℕ)
    (h : ∀ i : Fin n, a[i.val]! ^^^ b[i.val]! = c[i.val]!) :
    decode n a + decode n b = decode n c := by
  ext i j
  change bit a[i.val]! j.val + bit b[i.val]! j.val = bit c[i.val]! j.val
  rw [← bit_xor, h i]

inductive Operation where
  | one
  | actor (a : Fin 2)
  | add (i j : ℕ)
  | mul (i j : ℕ)
  deriving Inhabited, DecidableEq

def Step (n : ℕ) (A : Fin 2 → Array ℕ) (data : Array (Array ℕ))
    (ops : Array Operation) (k : ℕ) : Prop :=
  match ops[k]! with
  | .one => ∀ r : Fin n, (data[k]!)[r.val]! = 2 ^ r.val
  | .actor a => data[k]! = A a
  | .add i j => i < k ∧ j < k ∧
      ∀ r : Fin n, (data[i]!)[r.val]! ^^^ (data[j]!)[r.val]! = (data[k]!)[r.val]!
  | .mul i j => i < k ∧ j < k ∧
      ∀ r : Fin n, rowProduct (data[i]!)[r.val]! data[j]! n = (data[k]!)[r.val]!

instance (n : ℕ) (A : Fin 2 → Array ℕ) (data : Array (Array ℕ))
    (ops : Array Operation) (k : ℕ) : Decidable (Step n A data ops k) := by
  unfold Step
  split <;> infer_instance

theorem certificate_mem (n N : ℕ) (A : Fin 2 → Array ℕ) (data : Array (Array ℕ))
    (ops : Array Operation) (hstep : ∀ k : Fin N, Step n A data ops k.val)
    (Q : Subalgebra (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)))
    (hA : ∀ a, decode n (A a) ∈ Q) (k : ℕ) (hk : k < N) : decode n data[k]! ∈ Q := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hs := hstep ⟨k, hk⟩
    unfold Step at hs
    split at hs
    · have he : decode n data[k]! = 1 := by
        ext i j
        change bit (data[k]!)[i.val]! j.val = _
        rw [hs i]
        simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]
      rw [he]
      exact Q.one_mem
    · rw [hs]
      exact hA _
    · obtain ⟨hi, hj, he⟩ := hs
      rw [← decode_add n _ _ _ he]
      exact Q.add_mem (ih _ hi (hi.trans hk)) (ih _ hj (hj.trans hk))
    · obtain ⟨hi, hj, he⟩ := hs
      rw [← decode_mul n _ _ _ he]
      exact Q.mul_mem (ih _ hi (hi.trans hk)) (ih _ hj (hj.trans hk))

def vectorColumn (n c : ℕ) : Array ℕ :=
  Array.ofFn (fun i : Fin n => if c.testBit i.val then 1 else 0)

theorem bit_vectorColumn (n c : ℕ) (i : Fin n) :
    bit (vectorColumn n c)[i.val]! 0 = bit c i.val := by
  have he : (vectorColumn n c)[i.val]! = if c.testBit i.val then 1 else 0 := by
    simp [vectorColumn, getElem!_pos]
  rw [he]
  cases h : c.testBit i.val <;> simp [bit, h]

theorem decode_mulVec (n : ℕ) (a : Array ℕ) (c v : ℕ)
    (h : ∀ i : Fin n, rowProduct a[i.val]! (vectorColumn n c) n =
      if v.testBit i.val then 1 else 0) :
    decode n a *ᵥ (fun i : Fin n => bit c i.val) = fun i : Fin n => bit v i.val := by
  funext i
  change (∑ j : Fin n, bit a[i.val]! j.val * bit c j.val) = _
  simp_rw [← bit_vectorColumn n c]
  rw [Fin.sum_univ_eq_sum_range (fun j => bit a[i.val]! j *
    bit (vectorColumn n c)[j]! 0), ← bit_rowProduct, h i]
  cases hi : v.testBit i.val <;> simp [bit, hi]

theorem decode_mulVec_of_column (n : ℕ) (a b : Array ℕ) (c v : ℕ)
    (hb : ∀ i : Fin n, bit b[i.val]! 0 = bit c i.val)
    (h : ∀ i : Fin n, rowProduct a[i.val]! b n =
      if v.testBit i.val then 1 else 0) :
    decode n a *ᵥ (fun i : Fin n => bit c i.val) = fun i : Fin n => bit v i.val := by
  funext i
  change (∑ j : Fin n, bit a[i.val]! j.val * bit c j.val) = _
  simp_rw [← hb]
  rw [Fin.sum_univ_eq_sum_range (fun j => bit a[i.val]! j * bit b[j]! 0),
    ← bit_rowProduct, h i]
  cases hi : v.testBit i.val <;> simp [bit, hi]

theorem decode_vecMul (n : ℕ) (a : Array ℕ) (r v : ℕ)
    (h : rowProduct r a n = v) :
    (fun i : Fin n => bit r i.val) ᵥ* decode n a = fun i : Fin n => bit v i.val := by
  funext i
  change (∑ j : Fin n, bit r j.val * bit a[j.val]! i.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun j => bit r j * bit a[j]! i.val),
    ← bit_rowProduct, h]

section Density
variable {K : Type*} [CommSemiring K] {n : Type*} [Fintype n] [DecidableEq n]

theorem density_of_outer_basis
    (Q : Subalgebra K (Matrix n n K)) (U X V Y : Matrix n n K)
    (hUX : U * X = 1) (hYV : Y * V = 1)
    (houter : ∀ i j, Matrix.vecMulVec (fun k => U k i) (V j) ∈ Q) : Q = ⊤ := by
  apply top_unique
  intro M _
  have hid : M = U * (X * M * Y) * V := by
    simp only [← mul_assoc, hUX, one_mul]
    rw [mul_assoc, hYV, mul_one]
  rw [hid, Matrix.matrix_eq_sum_single (X * M * Y), Finset.mul_sum, Finset.sum_mul]
  apply Q.sum_mem
  intro i _
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Q.sum_mem
  intro j _
  have he (a : K) : U * Matrix.single i j a * V =
      a • Matrix.vecMulVec (fun k => U k i) (V j) := by
    ext k l
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.vecMulVec_apply,
      ite_and, mul_comm, mul_left_comm]
  rw [he]
  exact Q.smul_mem (houter i j) _

theorem density_of_rank_one
    (Q : Subalgebra K (Matrix n n K)) (c r : n → K)
    (hcr : Matrix.vecMulVec c r ∈ Q)
    (L R : n → Matrix n n K) (hL : ∀ i, L i ∈ Q) (hR : ∀ i, R i ∈ Q)
    (U X V Y : Matrix n n K) (hUX : U * X = 1) (hYV : Y * V = 1)
    (hc : ∀ i, L i *ᵥ c = fun k => U k i)
    (hr : ∀ j, r ᵥ* R j = V j) : Q = ⊤ := by
  apply density_of_outer_basis Q U X V Y hUX hYV
  intro i j
  have h := Q.mul_mem (Q.mul_mem (hL i) hcr) (hR j)
  rwa [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hc, hr] at h

end Density

section Extension
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (F : Type*) [Field F] [CharP F 2]

def castMatrix : Matrix n n (ZMod 2) →+* Matrix n n F :=
  (ZMod.castHom (dvd_refl 2) F).mapMatrix

theorem density_cast (A : Fin 2 → Matrix n n (ZMod 2))
    (hdense : ∀ Q : Subalgebra (ZMod 2) (Matrix n n (ZMod 2)),
      (∀ i, A i ∈ Q) → Q = ⊤)
    (S : Subalgebra F (Matrix n n F))
    (hA : ∀ i, castMatrix F (A i) ∈ S) : S = ⊤ := by
  let := ZMod.algebra F 2
  let φ : Matrix n n (ZMod 2) →ₐ[ZMod 2] Matrix n n F :=
    (Algebra.ofId (ZMod 2) F).mapMatrix
  let Q := (S.restrictScalars (ZMod 2)).comap φ
  have hQ : Q = ⊤ := hdense Q hA
  have hunit (i j : n) : Matrix.single i j (1 : F) ∈ S := by
    have hm : Matrix.single i j (1 : ZMod 2) ∈ Q := by rw [hQ]; trivial
    change φ (Matrix.single i j (1 : ZMod 2)) ∈ S at hm
    simpa [φ, Matrix.single_apply] using hm
  apply top_unique
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  exact S.sum_mem (fun i _ => S.sum_mem (fun j _ => by
    simpa using S.smul_mem (hunit i j) (M i j)))

end Extension
end CycleCertificate
