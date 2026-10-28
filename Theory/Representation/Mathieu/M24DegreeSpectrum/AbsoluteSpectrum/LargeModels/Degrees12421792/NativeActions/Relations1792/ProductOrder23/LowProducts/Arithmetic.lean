module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.Arithmetic
public import Mathlib.Data.List.Forall2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.LowProducts.Core

/-!
# A checked lookup-table implementation of binary row multiplication

A table stores the sixteen XOR combinations of four consecutive right-hand
rows in base 2^1792. `ValidTable` requires every one of these entries to equal
the existing sequential XOR operation. Induction over all tables then proves
`masksCheck_eq`, so the numerical certificates return the original public
checker without a new matrix convention or an unchecked evaluator.

Matching the input mask before recursion evaluates each quotient once and
stops at zero. Literal base-2^32 masks bound the nested division depth. The complete-list consumer is `checks_flatten`, used by all
three product families. See `source/README.md` for the bounded measurements
and ATLAS M24G1-P1 word-2 source attribution.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.LowProducts.Arithmetic

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates

theorem skipRow_append (a : Nat) (bs cs : List Nat) :
    skipRow a (bs ++ cs) = skipRow a bs ^^^ skipRow (a / 2 ^ bs.length) cs := by
  induction bs generalizing a with
  | nil => simp [skipRow]
  | cons b bs ih =>
    simp only [List.cons_append, skipRow, List.length_cons, pow_succ',
      ← Nat.div_div_eq_div_mul, ih]
    split <;> simp_all [Nat.xor_assoc]

theorem skipRow_mod (a : Nat) (bs : List Nat) :
    skipRow (a % 2 ^ bs.length) bs = skipRow a bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, pow_succ', skipRow,
      Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self, ih]

def ValidTable (t : Nat) (b : List Nat) : Prop :=
  b.length = 4 ∧ ∀ i : Fin 16, tableEntry t i.val = skipRow i.val b

theorem skipRow_zero (b : List Nat) : skipRow 0 b = 0 := by
  induction b with
  | nil => rfl
  | cons b bs ih => simp [skipRow, ih]

theorem tableRow_eq (ts : List Nat) (bs : List (List Nat))
    (h : List.Forall₂ ValidTable ts bs) (a : Nat) :
    tableRow a ts = skipRow a bs.flatten := by
  induction h generalizing a with
  | nil => cases a <;> rfl
  | @cons t b ts bs h hs ih =>
    cases a with
    | zero => simp [tableRow, skipRow_zero]
    | succ a =>
      have hp : 2 ^ b.length = 16 := by rw [h.1]; rfl
      rw [tableRow, List.flatten_cons, skipRow_append,
        h.2 ⟨(a + 1) % 16, Nat.mod_lt _ (by decide)⟩, ih]
      change skipRow ((a + 1) % 16) b ^^^ _ = _
      rw [← hp, skipRow_mod]

/-- A group of lookup tables represents precisely 32 right-hand rows. -/
def ValidGroup (ts bs : List Nat) : Prop :=
  bs.length = 32 ∧ ∀ a, tableRow a ts = skipRow a bs

theorem validGroup_of_tables (ts : List Nat) (bs : List (List Nat))
    (h : List.Forall₂ ValidTable ts bs) (hlen : bs.flatten.length = 32) :
    ValidGroup ts bs.flatten := ⟨hlen, tableRow_eq ts bs h⟩

theorem masksRow_eq (ms : List Nat) (ts bs : List (List Nat))
    (h : List.Forall₂ ValidGroup ts bs) :
    masksRow ms ts = skipRow (packMasks ms) bs.flatten := by
  induction h generalizing ms with
  | nil => cases ms <;> rfl
  | @cons t b ts bs hb hs ih =>
    cases ms with
    | nil => simp [masksRow, packMasks, skipRow_zero]
    | cons m ms =>
      have hmod : packMasks (m :: ms) % 4294967296 = m % 4294967296 := by
        simp [packMasks]
      have hdiv : packMasks (m :: ms) / 4294967296 = packMasks ms := by
        simp [packMasks, Nat.add_div]
        exact Nat.mod_lt _ (by decide)
      rw [masksRow, hb.2, List.flatten_cons, skipRow_append,
        ← skipRow_mod (packMasks (m :: ms)) b, hb.1,
        show 2 ^ 32 = 4294967296 from rfl, hmod, hdiv, ih]

theorem masksCheck_eq (ms ts bs : List (List Nat)) (cs : List Nat)
    (h : List.Forall₂ ValidGroup ts bs) :
    masksCheck ms ts cs = checkSkip (ms.map packMasks) bs.flatten cs := by
  induction ms generalizing cs with
  | nil => cases cs <;> rfl
  | cons a as ih =>
    cases cs <;> simp [masksCheck, checkSkip, masksRow_eq _ _ _ h, ih]

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.Certificate

/-- Return the original complete checker from reconstructed digit witnesses. -/
theorem of_masks (xs zs : List Nat) (ts bs : List (List Nat))
    (h : List.Forall₂ ValidGroup ts bs)
    (hc : ∃ ms : List (List Nat),
      ms.map packMasks = xs ∧ masksCheck ms ts zs = true) :
    check xs bs.flatten zs = true := by
  obtain ⟨ms, rfl, hc⟩ := hc
  rwa [masksCheck_eq _ _ _ _ h] at hc

/-- Concatenate all the certified row blocks, retaining every row. -/
theorem checks_flatten (xs zs : List (List Nat)) (ys : List Nat)
    (h : List.Forall₂ (fun x z => check x ys z = true) xs zs) :
    check xs.flatten ys zs.flatten = true := by
  induction h with
  | nil => rfl
  | cons h hs ih => exact append _ _ _ _ _ h ih

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.LowProducts.Arithmetic
