module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.Arithmetic

/-!
# Certified sparse rows for the HS perturbation inverse

A sparse row is a list of positions and field coefficients. The checker
verifies its full packed encoding and its linear combination of inverse rows.
The sum identity below connects those checks to ordinary matrix multiplication.
This handles the first 560 rows of the literal ATLAS HSG1-f4r896aB0 singular
matrix without scanning all 896 coefficients for each sparse row.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
open Packed
abbrev Terms := List (ℕ × Row)
def combine : Terms → (ℕ → Row) → Row
  | [], _ => (0, 0)
  | (i, c) :: ts, b => Base.addRow (scaleRow c 0 (b i)) (combine ts b)

theorem sparse_product (ts : Terms) (n : ℕ) (b : Mat)
    (hs : ∀ t ∈ ts, t.1 < n) (j : ℕ) :
    decode (combine ts (fun i => b.getD i (0, 0))) j =
      ∑ k : Fin n, decode (combine ts unitRow) k.val * decode (b.getD k.val (0, 0)) j := by
  induction ts with
  | nil => simp [combine, decode, Base.entry_zero]
  | cons t ts ih =>
    obtain ⟨i, c⟩ := t
    have hi : i < n := hs (i, c) (by simp)
    have ht : ∀ t ∈ ts, t.1 < n := fun t h => hs t (by simp [h])
    simp only [combine, decode_add, decode_scaleRow, decode_unitRow, add_mul,
      Finset.sum_add_distrib]
    rw [ih ht]
    congr 1
    have he (k : Fin n) : (if i = k.val then (1 : Four) else 0) =
        if k = (⟨i, hi⟩ : Fin n) then 1 else 0 := by
      simp only [Fin.ext_iff]
      exact if_congr eq_comm rfl rfl
    simp_rw [he, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp
def checkSparse (n : ℕ) : List Terms → Mat → Mat → Mat → Bool
  | [], [], _, [] => true
  | t :: ts, a :: as, b, c :: cs =>
      (t.all fun x => decide (x.1 < n)) &&
      ((combine t unitRow == a) &&
      ((combine t (fun i => b.getD i (0, 0)) == c) && checkSparse n ts as b cs))
  | _, _, _, _ => false

theorem checkSparse_get (n : ℕ) (ts : List Terms) (a b c : Mat)
    (h : checkSparse n ts a b c = true) (i : ℕ) (hi : i < a.length) (j : ℕ) :
    (∑ k : Fin n, decode (a.getD i (0, 0)) k.val * decode (b.getD k.val (0, 0)) j) =
      decode (c.getD i (0, 0)) j := by
  induction a generalizing ts c i with
  | nil => simp at hi
  | cons a as ih =>
    cases ts with
    | nil => simp [checkSparse] at h
    | cons t ts =>
      cases c with
      | nil => simp [checkSparse] at h
      | cons c cs =>
        simp only [checkSparse, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨hn, ha, hc, hr⟩ := h
        cases i with
        | zero =>
          simp only [List.getD_cons_zero]
          rw [← ha, ← hc]
          exact (sparse_product t n b (by simpa only [List.all_eq_true, decide_eq_true_eq] using hn) j).symm
        | succ i =>
          simpa only [List.getD_cons_succ] using ih ts cs hr i (Nat.lt_of_succ_lt_succ hi)


theorem checkSparse_append (n : ℕ) (ts us : List Terms) (a a' b c c' : Mat)
    (h : checkSparse n ts a b c = true) (h' : checkSparse n us a' b c' = true) :
    checkSparse n (ts ++ us) (a ++ a') b (c ++ c') = true := by
  induction ts generalizing a c with
  | nil => cases a <;> cases c <;> simp_all [checkSparse]
  | cons t ts ih =>
    cases a with
    | nil => simp [checkSparse] at h
    | cons a as =>
      cases c with
      | nil => simp [checkSparse] at h
      | cons c cs =>
        simp only [checkSparse, Bool.and_eq_true] at h
        simp only [List.cons_append, checkSparse, h.1, h.2.1, h.2.2.1,
          Bool.true_and]
        exact ih as cs h.2.2.2

theorem checkSparse_drop_split (n : ℕ) (ts : List Terms) (a b c : Mat) (i k : ℕ)
    (h₁ : checkSparse n ((ts.drop i).take k) ((a.drop i).take k) b
      ((c.drop i).take k) = true)
    (h₂ : checkSparse n (ts.drop (i + k)) (a.drop (i + k)) b
      (c.drop (i + k)) = true) :
    checkSparse n (ts.drop i) (a.drop i) b (c.drop i) = true := by
  have h₂' : checkSparse n ((ts.drop i).drop k) ((a.drop i).drop k) b
      ((c.drop i).drop k) = true := by simpa only [List.drop_drop] using h₂
  have h := checkSparse_append n _ _ _ _ _ _ _ h₁ h₂'
  simpa only [List.take_append_drop] using h

theorem eval_product_of_sparse_prefix (n m : ℕ) (ts : List Terms) (a b c : Mat)
    (ha : a.length = n) (hb : b.length = n)
    (hs : checkSparse n ts (a.take m) b (c.take m) = true)
    (hd : checkRows (a.drop m) b (c.drop m) = true) :
    eval n a * eval n b = eval n c := by
  funext i j
  change (∑ k : Fin n, decode (a.getD i.val (0, 0)) k.val *
    decode (b.getD k.val (0, 0)) j.val) = decode (c.getD i.val (0, 0)) j.val
  by_cases hi : i.val < m
  · have h := checkSparse_get n ts (a.take m) b (c.take m) hs i.val
      (by simp only [List.length_take, ha]; omega) j.val
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_take, hi, if_true] using h
  · have him : m ≤ i.val := Nat.le_of_not_gt hi
    have h := checkRows_get (a.drop m) b (c.drop m) hd (i.val - m)
      (by simp only [List.length_drop, ha]; omega)
    have he := congrArg (fun r : Row => decode r j.val) h
    rw [product_eq, decode_rowProduct _ _ n hb] at he
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_sub_of_le him] using he

end Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
