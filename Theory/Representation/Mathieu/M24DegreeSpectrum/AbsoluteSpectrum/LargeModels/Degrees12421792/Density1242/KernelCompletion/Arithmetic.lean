module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.Seed
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.Arithmetic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Soundness for the degree-1242 packed certificates

The sequential row evaluator is the existing J₂ arithmetic evaluator. Its
soundness identifies each checked row with multiplication over `ZMod 2`.
The scalar evaluator and bounded-range composition below handle the paired
kernels and assemble small certificates without repeating large reductions.
Application: the literal ATLAS M24 degree-1242 data, James (1973), pp. 57–111.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.KernelCompletion
open Thompson.BinaryMatrix
abbrev packedMul := Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.row
abbrev bit_packedMul := Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.bit_row_array

def checkRange (p : ℕ → Bool) (start count : ℕ) : Bool :=
  (List.range' start count).all p

theorem checkRange_sound {p : ℕ → Bool} {start count i : ℕ}
    (h : checkRange p start count = true) (hi : start ≤ i) (hi' : i < start + count) :
    p i = true := by
  apply List.all_eq_true.mp h i
  exact List.mem_range'.mpr ⟨i - start, by omega, by omega⟩

theorem checkRange_join {p : ℕ → Bool} {start m n : ℕ}
    (h₁ : checkRange p start m = true)
    (h₂ : checkRange p (start + m) n = true) :
    checkRange p start (m + n) = true := by
  apply List.all_eq_true.mpr
  intro i hi
  obtain ⟨k, hk, rfl⟩ := List.mem_range'.mp hi
  by_cases h : k < m
  · exact checkRange_sound h₁ (by omega) (by omega)
  · exact checkRange_sound h₂ (by omega) (by omega)

def packedDot (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => packedDot a b n ^^^ (if a.testBit n then if b.testBit n then 1 else 0 else 0)

theorem bit_packedDot (a b n : ℕ) :
    bit (packedDot a b n) 0 = ∑ i : Fin n, bit a i.val * bit b i.val := by
  induction n with
  | zero => simp [packedDot, bit]
  | succ n ih =>
    rw [packedDot, bit_xor, ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    congr 1
    cases ha : a.testBit n <;> cases hb : b.testBit n <;> simp [bit, ha, hb]

theorem product_of_rows {n : ℕ} (a b c : Array ℕ) (hb : b.size = n)
    (h : ∀ i : Fin n, packedMul a[i.val]! b.toList 0 = c[i.val]!) :
    decode n a * decode n b = decode n c := by
  ext i j
  change (∑ k : Fin n, bit a[i.val]! k.val * bit b[k.val]! j.val) = bit c[i.val]! j.val
  rw [← bit_packedMul n b hb]
  change bit (packedMul a[i.val]! b.toList 0) j.val = _
  rw [h i]

theorem inverse_of_rows {n : ℕ} (a b : Array ℕ) (hb : b.size = n)
    (h : ∀ i : Fin n, packedMul a[i.val]! b.toList 0 = 2 ^ i.val) :
    decode n a * decode n b = 1 := by
  ext i j
  change (∑ k : Fin n, bit a[i.val]! k.val * bit b[k.val]! j.val) = _
  rw [← bit_packedMul n b hb]
  change bit (packedMul a[i.val]! b.toList 0) j.val = _
  rw [h i]
  simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.KernelCompletion
