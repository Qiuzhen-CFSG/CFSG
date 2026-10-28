module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.LiteralProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
/-!
# Bounded certificates for the degree-1242 generator orders

The carry-free checker expands each column to base 2048, adds selected rows,
and takes each digit modulo two. Its proved soundness applies because 1242 is
less than 2048. One-coordinate inputs use the original checked row-selection
shortcut. The expansion table has its own checked shortcut for powers of two.

The consumers are the literal square and cube in `GeneratorOrders`. Neither
an action nor an order or presentation premise enters this arithmetic.
Source: ATLAS M24G1-f2r1242B0.m1/.m2 and M24G1-P1; see `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.GeneratorOrders
open Thompson.BinaryMatrix
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair

/-- A sequential range avoids reducing dependent finite-vector enumeration
in the concrete identity-table checks. -/
theorem decode_range_identity (n : Nat) :
    decode n ((List.range n).map (fun i => 2^i)).toArray = 1 := by
  ext i j
  simp [decode, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

theorem expand_zero (n : Nat) : Relations1792.Arithmetic.expand n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Relations1792.Arithmetic.expand, ih]

theorem expand_single (n k : Nat) (h : k < n) :
    Relations1792.Arithmetic.expand n (2^k) = 2048^k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => simp [Relations1792.Arithmetic.expand, expand_zero]
    | succ k =>
      rw [Relations1792.Arithmetic.expand]
      simp only [pow_succ', Nat.mul_mod_right, Nat.zero_add]
      rw [Nat.mul_comm 2, Nat.mul_div_left _ (by decide), ih k (by omega)]

def wideCheck (width blocks : Nat) : List Nat → List Nat → List (Option Nat) → Bool
  | [], [], [] => true
  | a::as, c::cs, hint::hs =>
    (match hint with
      | some k => (a == 2^k) && (k < width * blocks) && (c == 2048^k)
      | none => Relations1792.Arithmetic.expandBlocks width blocks a == c) &&
      wideCheck width blocks as cs hs
  | _, _, _ => false

theorem wideCheck_sound (width blocks : Nat) (as cs : List Nat) (hs : List (Option Nat))
    (h : wideCheck width blocks as cs hs = true) :
    as.map (Relations1792.Arithmetic.expandBlocks width blocks) = cs := by
  induction as generalizing cs hs with
  | nil => cases cs <;> cases hs <;> simp_all [wideCheck]
  | cons a as ih =>
    cases cs with
    | nil => cases hs <;> simp [wideCheck] at h
    | cons c cs =>
      cases hs with
      | nil => simp [wideCheck] at h
      | cons hint hs =>
        simp only [wideCheck, Bool.and_eq_true] at h
        rw [List.map_cons, ih cs hs h.2]
        congr 1
        cases hint with
        | none => exact of_decide_eq_true h.1
        | some k =>
          have hh : (a = 2^k ∧ k < width * blocks) ∧ c = 2048^k := by simpa using h.1
          rw [Relations1792.Arithmetic.expandBlocks_eq, hh.1.1,
            expand_single _ _ hh.1.2, hh.2]


def rowCheck (width blocks a : Nat) (bs : List Nat) (wide : List (List Nat))
    (c : Nat) : Option Nat → Bool
  | some k => (a == 2^k) && (bs[k]! == c)
  | none => Relations1792.Arithmetic.compressBlocks width blocks (Relations1792.Arithmetic.accumChunks a wide) == c

def check (width blocks : Nat) : List Nat → List Nat → List (List Nat) →
    List Nat → List (Option Nat) → Bool
  | [], _, _, [], [] => true
  | a::as, bs, wide, c::cs, hint::hs =>
    rowCheck width blocks a bs wide c hint && check width blocks as bs wide cs hs
  | _, _, _, _, _ => false

theorem rowCheck_sound (width blocks a : Nat) (bs : List Nat) (wide : List (List Nat))
    (c : Nat) (hint : Option Nat) (hn : width * blocks < 2048)
    (hb : bs.length = width * blocks)
    (hw : wide.flatten = bs.map (Relations1792.Arithmetic.expandBlocks width blocks))
    (h : rowCheck width blocks a bs wide c hint = true) (j : Fin (width * blocks)) :
    bit c j.val = ∑ k : Fin (width * blocks), bit a k.val * bit bs[k.val]! j.val := by
  cases hint with
  | some k =>
    have hh : a = 2^k ∧ bs[k]! = c := by simpa [rowCheck] using h
    have hp := bit_row_array (width * blocks) bs.toArray (by simpa using hb) a j.val
    simp only [← shiftRow_eq_row, hh.1, shiftRow_single, hh.2] at hp
    simpa [hh.1] using hp
  | none =>
    have hc : Relations1792.Arithmetic.compress (width * blocks) (Relations1792.Arithmetic.accum a wide.flatten) = c := by
      simpa only [rowCheck, Relations1792.Arithmetic.compressBlocks_eq, Relations1792.Arithmetic.accumChunks_eq, beq_iff_eq] using h
    have he : Relations1792.Arithmetic.expandBlocks width blocks = Relations1792.Arithmetic.expand (width * blocks) :=
      funext (Relations1792.Arithmetic.expandBlocks_eq width blocks)
    rw [he] at hw
    have hlist : List.ofFn (fun k : Fin (width * blocks) => bs[k.val]!) = bs := by
      simpa only [hb, Fin.val_cast] using Relations1792.Arithmetic.ofFn_get! bs
    have hwide : wide.flatten = List.ofFn
        (fun k : Fin (width * blocks) => Relations1792.Arithmetic.expand (width * blocks) bs[k.val]!) := by
      rw [hw]
      simpa only [List.map_ofFn, Function.comp_def] using
        congrArg (List.map (Relations1792.Arithmetic.expand (width * blocks))) hlist.symm
    rw [← hc, hwide]
    exact Relations1792.Arithmetic.bit_product (width * blocks) a hn (fun k => bs[k.val]!) j

theorem check_get (width blocks : Nat) (as bs cs : List Nat) (wide : List (List Nat))
    (hs : List (Option Nat)) (h : check width blocks as bs wide cs hs = true)
    (i : Nat) (hi : i < as.length) :
    rowCheck width blocks as[i]! bs wide cs[i]! hs[i]! = true := by
  induction as generalizing cs hs i with
  | nil => simp at hi
  | cons a as ih =>
    cases cs with
    | nil => cases hs <;> simp [check] at h
    | cons c cs =>
      cases hs with
      | nil => simp [check] at h
      | cons hint hs =>
        simp only [check, Bool.and_eq_true] at h
        cases i with
        | zero => simpa using h.1
        | succ i => simpa using ih cs hs h.2 i (Nat.lt_of_succ_lt_succ hi)

theorem check_append (width blocks : Nat) (a₁ a₂ bs c₁ c₂ : List Nat)
    (wide : List (List Nat)) (h₁ h₂ : List (Option Nat))
    (p₁ : check width blocks a₁ bs wide c₁ h₁ = true)
    (p₂ : check width blocks a₂ bs wide c₂ h₂ = true) :
    check width blocks (a₁ ++ a₂) bs wide (c₁ ++ c₂) (h₁ ++ h₂) = true := by
  induction a₁ generalizing c₁ h₁ with
  | nil => cases c₁ <;> cases h₁ <;> simp_all [check]
  | cons a as ih =>
    cases c₁ with
    | nil => cases h₁ <;> simp [check] at p₁
    | cons c cs =>
      cases h₁ with
      | nil => simp [check] at p₁
      | cons hint hs =>
        simp only [check, Bool.and_eq_true] at p₁
        simp only [List.cons_append, check, Bool.and_eq_true]
        exact ⟨p₁.1, ih cs hs p₁.2⟩

theorem product (width blocks : Nat) (as bs cs : List Nat) (wide : List (List Nat))
    (hs : List (Option Nat)) (hn : width * blocks < 2048)
    (ha : as.length = width * blocks) (hb : bs.length = width * blocks)
    (hw : wide.flatten = bs.map (Relations1792.Arithmetic.expandBlocks width blocks))
    (h : check width blocks as bs wide cs hs = true) :
    decode (width * blocks) as.toArray * decode (width * blocks) bs.toArray =
      decode (width * blocks) cs.toArray := by
  ext i j
  have hp := rowCheck_sound width blocks as[i.val]! bs wide cs[i.val]! hs[i.val]!
    hn hb hw (check_get width blocks as bs cs wide hs h i.val (by simp [ha])) j
  simpa [decode, Matrix.mul_apply] using hp.symm
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.GeneratorOrders
