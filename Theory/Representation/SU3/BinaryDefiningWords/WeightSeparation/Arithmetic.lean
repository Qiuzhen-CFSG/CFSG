module
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.FixedLine.PolynomialModel
public import Mathlib.FieldTheory.Finite.Basic
/-!
# Recovering binary unitary words from their torus exponents

For a word of length s, its binary weight pair (A,B) lies in [0,2^s)².
The exponent qA+B, q=2^s, determines every letter. On the multiplicative
group of a field of order q², equal power characters determine this exponent
modulo q²-1. Its only possible collision in the closed interval [0,q²-1]
is between the all-trivial and all-adjoint words. Their concrete carrier
dimensions, 1 and 8^s, distinguish them when s is positive.

This is the arithmetic part of separation for the literal restricted tensor
words of GLS III, 2.8.2, 2.8.6(a), and 2.8.10(c). The unitary consumer supplies
character equality from an intertwiner and its upper fixed-line geometry.
-/

@[expose] public section
namespace Representation.SU3.BinaryDefiningWords.WeightSeparation
open Representation.SL3.BinaryDefiningFactors
open Representation.SL3.BinaryDefiningFactors.TensorSimplicity.FixedLine

theorem weight_injective (v w : List Factor) (hlen : v.length = w.length)
    (hweight : wordWeight v = wordWeight w) : v = w := by
  induction v generalizing w with
  | nil => simpa using hlen.symm
  | cons a v ih =>
    cases w with
    | nil => simp at hlen
    | cons b w =>
      have h0 := congrArg Prod.fst hweight
      have h1 := congrArg Prod.snd hweight
      have hab : a = b := by
        cases a <;> cases b <;> simp_all [wordWeight] <;> omega
      subst b
      congr 1
      apply ih w (by simpa using hlen)
      apply Prod.ext <;> simp only [wordWeight] at h0 h1 <;> omega

def exponent (q : ℕ) (w : List Factor) : ℕ := q * (wordWeight w).1 + (wordWeight w).2

theorem exponent_injective (s : ℕ) (v w : List Factor)
    (hv : v.length = s) (hw : w.length = s)
    (he : exponent (2 ^ s) v = exponent (2 ^ s) w) : v = w := by
  have hvb := (wordWeight_lt v).2
  have hwb := (wordWeight_lt w).2
  rw [hv] at hvb
  rw [hw] at hwb
  have hb := congrArg (fun n => n % (2 ^ s)) he
  simp only [exponent, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add,
    Nat.mod_eq_of_lt hvb, Nat.mod_eq_of_lt hwb] at hb
  apply weight_injective v w (hv.trans hw.symm)
  apply Prod.ext
  · dsimp [exponent] at he
    rw [hb] at he
    exact Nat.eq_of_mul_eq_mul_left (by positivity) (Nat.add_right_cancel he)
  · exact hb

theorem exponent_le (s : ℕ) (w : List Factor) (hw : w.length = s) :
    exponent (2 ^ s) w ≤ (2 ^ s) ^ 2 - 1 := by
  obtain ⟨ha, hb⟩ := wordWeight_lt w
  rw [hw] at ha hb
  have hq : 0 < 2 ^ s := by positivity
  have hsq : (2 ^ s) ^ 2 - 1 + 1 = (2 ^ s) ^ 2 := Nat.sub_add_cancel (Nat.succ_le_of_lt (by positivity))
  dsimp [exponent]
  have hm := Nat.mul_le_mul_left (2 ^ s) (show (wordWeight w).1 + 1 ≤ 2 ^ s by omega)
  nlinarith

theorem weight_replicate_trivial (s : ℕ) : wordWeight (List.replicate s .trivial) = (0, 0) := by
  induction s with
  | zero => rfl
  | succ s ih => simp [List.replicate_succ, wordWeight, ih]

theorem weight_replicate_adjoint (s : ℕ) :
    wordWeight (List.replicate s .adjoint) = (2 ^ s - 1, 2 ^ s - 1) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have hq : 0 < 2 ^ s := by positivity
    simp only [List.replicate_succ, wordWeight, ih, pow_succ,
      reduceCtorEq, or_true, ite_true, Prod.mk.injEq]
    omega

theorem exponent_replicate_trivial (s : ℕ) :
    exponent (2 ^ s) (List.replicate s .trivial) = 0 := by
  simp [exponent, weight_replicate_trivial]

theorem exponent_replicate_adjoint (s : ℕ) :
    exponent (2 ^ s) (List.replicate s .adjoint) = (2 ^ s) ^ 2 - 1 := by
  have hq : 0 < 2 ^ s := by positivity
  rw [exponent, weight_replicate_adjoint]
  dsimp
  have hsq : (2 ^ s) ^ 2 - 1 + 1 = (2 ^ s) ^ 2 := Nat.sub_add_cancel (Nat.succ_le_of_lt (by positivity))
  have hsub : 2 ^ s - 1 + 1 = 2 ^ s := by omega
  nlinarith

theorem eq_trivial_of_exponent_zero (s : ℕ) (w : List Factor) (hw : w.length = s)
    (he : exponent (2 ^ s) w = 0) : w = List.replicate s .trivial := by
  apply exponent_injective s w _ hw (List.length_replicate ..)
  rw [he, exponent_replicate_trivial]

theorem eq_adjoint_of_exponent_max (s : ℕ) (w : List Factor) (hw : w.length = s)
    (he : exponent (2 ^ s) w = (2 ^ s) ^ 2 - 1) : w = List.replicate s .adjoint := by
  apply exponent_injective s w _ hw (List.length_replicate ..)
  rw [he, exponent_replicate_adjoint]

theorem eq_of_modEq_and_degree (s : ℕ) (hs : 0 < s) (v w : List Factor)
    (hv : v.length = s) (hw : w.length = s)
    (he : Nat.ModEq ((2 ^ s) ^ 2 - 1) (exponent (2 ^ s) v) (exponent (2 ^ s) w))
    (hd : wordDegree v = wordDegree w) : v = w := by
  have hvle := exponent_le s v hv
  have hwle := exponent_le s w hw
  have hdim : 1 < 8 ^ s := one_lt_pow₀ (by decide) (by omega)
  by_cases hvm : exponent (2 ^ s) v = (2 ^ s) ^ 2 - 1
  · by_cases hwm : exponent (2 ^ s) w = (2 ^ s) ^ 2 - 1
    · exact exponent_injective s v w hv hw (hvm.trans hwm.symm)
    · have hwlt : exponent (2 ^ s) w < (2 ^ s) ^ 2 - 1 := by omega
      have hwz : exponent (2 ^ s) w = 0 := by
        simpa [Nat.ModEq, hvm, Nat.mod_eq_of_lt hwlt] using he.symm
      rw [eq_adjoint_of_exponent_max s v hv hvm, eq_trivial_of_exponent_zero s w hw hwz] at hd
      simp [wordDegree, Factor.dimension] at hd
      omega
  · have hvlt : exponent (2 ^ s) v < (2 ^ s) ^ 2 - 1 := by omega
    by_cases hwm : exponent (2 ^ s) w = (2 ^ s) ^ 2 - 1
    · have hvz : exponent (2 ^ s) v = 0 := by
        simpa [Nat.ModEq, hwm, Nat.mod_eq_of_lt hvlt] using he
      rw [eq_trivial_of_exponent_zero s v hv hvz, eq_adjoint_of_exponent_max s w hw hwm] at hd
      simp [wordDegree, Factor.dimension] at hd
      omega
    · have hwlt : exponent (2 ^ s) w < (2 ^ s) ^ 2 - 1 := by omega
      apply exponent_injective s v w hv hw
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hvlt, Nat.mod_eq_of_lt hwlt] using he

theorem eq_of_unit_powers_and_degree {F : Type*} [Field F] [Finite F]
    (s : ℕ) (hs : 0 < s) (hcard : Nat.card F = (2 ^ s) ^ 2)
    (v w : List Factor) (hv : v.length = s) (hw : w.length = s)
    (he : ∀ k : Fˣ, k ^ exponent (2 ^ s) v = k ^ exponent (2 ^ s) w)
    (hd : wordDegree v = wordDegree w) : v = w := by
  obtain ⟨k, hk⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  apply eq_of_modEq_and_degree s hs v w hv hw _ hd
  have h := (pow_eq_pow_iff_modEq.mp (he k))
  rw [hk] at h
  have hc : Nat.card Fˣ = (2 ^ s) ^ 2 - 1 := by
    rw [Nat.card_units, hcard]
  rwa [hc] at h
end Representation.SU3.BinaryDefiningWords.WeightSeparation
