module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Mathlib.Data.List.OfFn
public import Mathlib.Tactic.Ring

/-!
# Carry-free arithmetic for packed binary matrix products

Encode each binary row as base-4096 digits. A selected-row sum of fewer than
4096 rows has no carries, so the parity of each digit is precisely the matrix
product over `ZMod 2`. The expanded row tables are untrusted input: a sequential
checker first relates every expanded digit to the original binary row.

`product_sound` verifies the actual decoded matrices. `checkRows_append` allows
bounded certificates to be combined without repeating indexed traversal.
`sum_sound` supports the concrete singular-expression recombination.
The proof is independent of any group, rank, kernel or representation hypothesis.
See `source/README.md` for the degree-1792 application and measured probes.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.Wide
open Thompson.BinaryMatrix

def coeffs : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n+1, f => f 0 + 4096 * coeffs n (fun i => f i.succ)

theorem coeffs_add (n : Nat) (f g : Fin n → Nat) :
    coeffs n (fun i => f i + g i) = coeffs n f + coeffs n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [coeffs, ih]; omega

theorem coeffs_zero (n : Nat) : coeffs n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [coeffs, ih]

theorem coeffs_sum {m : Nat} (n : Nat) (f : Fin m → Fin n → Nat) :
    coeffs n (fun j => ∑ i, f i j) = ∑ i, coeffs n (f i) := by
  induction m with
  | zero => simp [coeffs_zero]
  | succ m ih => simp only [Fin.sum_univ_succ, coeffs_add, ih]

theorem coeffs_digit (n : Nat) (f : Fin n → Nat) (hf : ∀ j, f j < 4096)
    (j : Fin n) : coeffs n f / 4096^j.val % 4096 = f j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [coeffs, Nat.add_mod, Nat.mod_eq_of_lt (hf 0)]
    · simp only [coeffs, Fin.val_succ, Nat.pow_succ']
      rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by decide),
        Nat.div_eq_of_lt (hf 0), Nat.zero_add]
      exact ih _ (fun i => hf i.succ) j

def digit (x j : Nat) : Nat := (x / 2^j) % 2

theorem digit_eq (x j : Nat) : digit x j = (x.testBit j).toNat := by
  exact (Nat.toNat_testBit _ _).symm

theorem digit_lt (x j : Nat) : digit x j < 2 := Nat.mod_lt _ (by decide)

def spread (n x : Nat) : Nat := coeffs n (fun j => digit x j.val)

def checkSpread : Nat → Nat → Nat → Bool
  | 0, _, w => w == 0
  | n+1, x, w => (x % 2 == w % 4096) && checkSpread n (x / 2) (w / 4096)

theorem digit_div (x j : Nat) : digit (x / 2) j = digit x (j+1) := by
  simp only [digit, Nat.div_div_eq_div_mul, Nat.pow_succ']

theorem spread_succ (n x : Nat) : spread (n+1) x = x % 2 + 4096 * spread n (x / 2) := by
  simp only [spread, coeffs, Fin.val_zero, digit, Nat.pow_zero, Nat.div_one, Fin.val_succ]
  congr 2
  congr 1
  funext i
  simp [Nat.div_div_eq_div_mul, Nat.pow_succ']

theorem checkSpread_sound (n x w : Nat) (h : checkSpread n x w = true) : w = spread n x := by
  induction n generalizing x w with
  | zero => simpa [checkSpread, spread, coeffs] using h
  | succ n ih =>
    simp only [checkSpread, Bool.and_eq_true, beq_iff_eq] at h
    rw [spread_succ, ← ih _ _ h.2, h.1]
    exact (Nat.mod_add_div w 4096).symm

def sumRow : Nat → List Nat → Nat
  | _, [] => 0
  | x, y :: ys => (if x % 2 == 1 then y else 0) + sumRow (x / 2) ys

theorem sumRow_ofFn (n : Nat) (x : Nat) (f : Fin n → Nat) :
    sumRow x (List.ofFn f) = ∑ i, digit x i.val * f i := by
  induction n generalizing x with
  | zero => simp [List.ofFn_zero, sumRow]
  | succ n ih =>
    rw [List.ofFn_succ, sumRow, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, digit_div]
    congr 1
    have h := digit_lt x 0
    simp only [digit, Nat.pow_zero, Nat.div_one] at h ⊢
    split_ifs with hx <;> simp_all

def checkParity : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | n+1, x, y => (x % 2 == y % 2) && checkParity n (x / 4096) (y / 2)

theorem checkParity_sound (n x y : Nat) (h : checkParity n x y = true)
    (j : Nat) (hj : j < n) : x / 4096^j % 2 = digit y j := by
  induction n generalizing x y j with
  | zero => omega
  | succ n ih =>
    simp only [checkParity, Bool.and_eq_true, beq_iff_eq] at h
    cases j with
    | zero => simpa [digit] using h.1
    | succ j =>
      simpa only [Nat.pow_succ', ← Nat.div_div_eq_div_mul, ← digit_div] using
        ih _ _ h.2 j (by omega)
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.Wide
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.Wide
open Thompson.BinaryMatrix

theorem coeffs_mul (n k : Nat) (f : Fin n → Nat) :
    coeffs n (fun j => k * f j) = k * coeffs n f := by
  induction n with
  | zero => simp [coeffs]
  | succ n ih => simp only [coeffs, ih]; ring

theorem sumRow_spread {n : Nat} (m x : Nat) (b : Fin n → Nat) :
    sumRow x (List.ofFn (fun i => spread m (b i))) =
      coeffs m (fun j => ∑ i, digit x i.val * digit (b i) j.val) := by
  rw [sumRow_ofFn, coeffs_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (coeffs_mul m (digit x i.val) _).symm

theorem bit_eq_digit (x j : Nat) : bit x j = (digit x j : ZMod 2) := by
  rw [digit_eq]
  cases h : x.testBit j <;> simp [bit, h]

theorem row_sound {n : Nat} (m x c : Nat) (b : Fin n → Nat)
    (hn : n < 4096)
    (h : checkParity m (sumRow x (List.ofFn (fun i => spread m (b i)))) c = true)
    (j : Fin m) : bit c j.val = ∑ i, bit x i.val * bit (b i) j.val := by
  rw [sumRow_spread] at h
  have hb (j : Fin m) : (∑ i, digit x i.val * digit (b i) j.val) < 4096 := by
    calc
      _ ≤ ∑ _ : Fin n, 1 := Finset.sum_le_sum fun i _ =>
        show digit x i.val * digit (b i) j.val ≤ 1 * 1 from
          Nat.mul_le_mul (by have := digit_lt x i.val; omega)
            (by have := digit_lt (b i) j.val; omega)
      _ = n := by simp
      _ < 4096 := hn
  have hp := checkParity_sound m _ c h j.val j.isLt
  have hd := coeffs_digit m _ hb j
  have hr : (∑ i, digit x i.val * digit (b i) j.val) % 2 = digit c j.val := by
    rw [← hd, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4096)]
    exact hp
  have hc := congrArg (fun z : Nat => (z : ZMod 2)) hr
  simpa only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_mod, ← bit_eq_digit] using hc.symm
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.Wide
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.Wide
open Thompson.BinaryMatrix

def checkSpreadRows (n : Nat) : List Nat → List Nat → Bool
  | [], [] => true
  | b :: bs, w :: ws => checkSpread n b w && checkSpreadRows n bs ws
  | _, _ => false

theorem checkSpreadRows_sound (n : Nat) (bs ws : List Nat)
    (h : checkSpreadRows n bs ws = true) : ws = bs.map (spread n) := by
  induction bs generalizing ws with
  | nil => cases ws <;> simp_all [checkSpreadRows]
  | cons b bs ih =>
    cases ws with
    | nil => simp [checkSpreadRows] at h
    | cons w ws =>
      simp only [checkSpreadRows, Bool.and_eq_true] at h
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨checkSpread_sound n b w h.1, ih ws h.2⟩

def checkRows (n : Nat) : List Nat → List Nat → List Nat → Bool
  | [], _, [] => true
  | a :: as, b, c :: cs => checkParity n (sumRow a b) c && checkRows n as b cs
  | _, _, _ => false

theorem checkRows_get (n : Nat) (a b c : List Nat) (h : checkRows n a b c = true)
    (i : Nat) (hi : i < a.length) : checkParity n (sumRow a[i]! b) c[i]! = true := by
  induction a generalizing c i with
  | nil => simp at hi
  | cons x xs ih =>
    cases c with
    | nil => simp [checkRows] at h
    | cons y ys =>
      simp only [checkRows, Bool.and_eq_true] at h
      cases i with
      | zero => simpa using h.1
      | succ i => simpa using ih _ h.2 i (Nat.lt_of_succ_lt_succ hi)

theorem product_sound (n : Nat) (a b w c : List Nat) (hn : n < 4096)
    (ha : a.length = n) (hb : b.length = n)
    (hw : checkSpreadRows n b w = true) (h : checkRows n a w c = true) :
    decode n a.toArray * decode n b.toArray = decode n c.toArray := by
  have he : b.map (spread n) = List.ofFn (fun i : Fin n => spread n b[i.val]!) := by
    rw [← hb]
    conv_lhs => rw [← List.ofFn_get b]
    rw [List.map_ofFn]
    congr 1
    funext i
    simp
  rw [checkSpreadRows_sound n b w hw, he] at h
  ext i j
  change (∑ k : Fin n, bit a.toArray[i.val]! k.val * bit b.toArray[k.val]! j.val) =
    bit c.toArray[i.val]! j.val
  simp only [List.getElem!_toArray]
  exact (row_sound n a[i.val]! c[i.val]! (fun k : Fin n => b[k.val]!) hn
    (checkRows_get n a _ c h i.val (by omega)) j).symm
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.Wide
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.Wide

theorem checkRows_append (n : Nat) (a₁ a₂ w c₁ c₂ : List Nat)
    (h₁ : checkRows n a₁ w c₁ = true) (h₂ : checkRows n a₂ w c₂ = true) :
    checkRows n (a₁ ++ a₂) w (c₁ ++ c₂) = true := by
  induction a₁ generalizing c₁ with
  | nil =>
    cases c₁ with
    | nil => exact h₂
    | cons _ _ => simp [checkRows] at h₁
  | cons x xs ih =>
    cases c₁ with
    | nil => simp [checkRows] at h₁
    | cons y ys =>
      simp only [checkRows, Bool.and_eq_true] at h₁
      simp only [List.cons_append, checkRows, Bool.and_eq_true]
      exact ⟨h₁.1, ih _ h₁.2⟩

def checkSum : List Nat → List Nat → List Nat → Bool
  | [], [], [] => true
  | a :: as, b :: bs, c :: cs => (a ^^^ b == c) && checkSum as bs cs
  | _, _, _ => false

theorem checkSum_get (a b c : List Nat) (h : checkSum a b c = true)
    (i : Nat) (hi : i < a.length) : a[i]! ^^^ b[i]! = c[i]! := by
  induction a generalizing b c i with
  | nil => simp at hi
  | cons x xs ih =>
    cases b with
    | nil => simp [checkSum] at h
    | cons y ys =>
      cases c with
      | nil => simp [checkSum] at h
      | cons z zs =>
        simp only [checkSum, Bool.and_eq_true, beq_iff_eq] at h
        cases i with
        | zero => simpa using h.1
        | succ i => simpa using ih _ _ h.2 i (Nat.lt_of_succ_lt_succ hi)

theorem sum_sound (n : Nat) (a b c : List Nat) (ha : a.length = n)
    (h : checkSum a b c = true) :
    Thompson.BinaryMatrix.decode n a.toArray + Thompson.BinaryMatrix.decode n b.toArray =
      Thompson.BinaryMatrix.decode n c.toArray := by
  ext i j
  change Thompson.BinaryMatrix.bit a.toArray[i.val]! j.val +
    Thompson.BinaryMatrix.bit b.toArray[i.val]! j.val =
    Thompson.BinaryMatrix.bit c.toArray[i.val]! j.val
  simp only [List.getElem!_toArray, ← Thompson.BinaryMatrix.bit_xor]
  rw [checkSum_get a b c h i.val (by omega)]
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.Wide
