module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.LiteralProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
/-!
# Checked carry-free products with sparse row shortcuts

For dense rows, the proved base-2048 arithmetic applies since 1242 < 2048.
For a one-coordinate row, a checked hint selects the corresponding stored row.
The two branches yield the same ordinary matrix product, in the original row
convention. Bounded row blocks can be concatenated without repeating checks.

The consumer is `ProductOrder23.FirstProduct`: the literal ATLAS product A B.
Sources: M24G1-P1 and M24G1-f2r1242B0.m1/.m2; see source/README.md.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23
open Thompson.BinaryMatrix
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
namespace CF
open Relations1792.Arithmetic

def check : List Nat → List Nat → List (List Nat) → List Nat → List (Option Nat) → Bool
  | [], _, _, [], [] => true
  | a::as, bs, wide, c::cs, hint::hs =>
    (match hint with
      | some k => (a == 2^k) && (bs[k]! == c)
      | none => compressBlocks 18 69 (accumChunks a wide) == c) &&
    check as bs wide cs hs
  | _, _, _, _, _ => false

theorem check_get (as bs : List Nat) (wide : List (List Nat)) (cs : List Nat)
    (hs : List (Option Nat)) (h : check as bs wide cs hs = true)
    (hb : bs.length = 1242)
    (hw : wide.flatten = bs.map (expandBlocks 18 69))
    (k : Nat) (hk : k < as.length) (j : Fin 1242) :
    bit cs[k]! j.val = ∑ i : Fin 1242, bit as[k]! i.val * bit bs[i.val]! j.val := by
  induction as generalizing cs hs k with
  | nil => simp at hk
  | cons a as ih =>
    cases cs with
    | nil => cases hs <;> simp [check] at h
    | cons c cs =>
      cases hs with
      | nil => simp [check] at h
      | cons hint hs =>
        simp only [check, Bool.and_eq_true] at h
        cases k with
        | succ k => exact ih cs hs h.2 k (Nat.lt_of_succ_lt_succ hk)
        | zero =>
          simp only [List.getElem!_cons_zero]
          cases hint with
          | some t =>
            have hh : a = 2^t ∧ bs[t]! = c := by simpa using h.1
            rw [← hh.2, ← shiftRow_single, shiftRow_eq_row]
            have hba : bs.toArray.size = 1242 := by simpa using hb
            simpa [hh.1] using
              bit_row_array 1242 bs.toArray hba (2^t) j.val
          | none =>
            have hh : compressBlocks 18 69 (accumChunks a wide) = c := by
              simpa using h.1
            rw [← hh, compressBlocks_eq, accumChunks_eq, hw]
            have hw' : bs.map (expandBlocks 18 69) =
                List.ofFn (fun i : Fin 1242 => expand 1242 bs[i.val]!) := by
              have he : expandBlocks 18 69 = expand 1242 := funext (expandBlocks_eq 18 69)
              rw [he]
              simpa only [List.map_ofFn, Function.comp_def, hb, Fin.val_cast] using
                congrArg (List.map (expand bs.length)) (ofFn_get! bs).symm
            rw [hw']
            exact bit_product 1242 a (by decide) (fun i => bs[i.val]!) j

set_option maxRecDepth 8192 in
theorem product (as bs : List Nat) (wide : List (List Nat)) (cs : List Nat)
    (hs : List (Option Nat)) (ha : as.length = 1242) (hb : bs.length = 1242)
    (hw : wide.flatten = bs.map (expandBlocks 18 69))
    (h : check as bs wide cs hs = true) :
    decode 1242 as.toArray * decode 1242 bs.toArray = decode 1242 cs.toArray := by
  ext i j
  change (∑ k : Fin 1242, bit as.toArray[i.val]! k.val *
    bit bs.toArray[k.val]! j.val) = bit cs.toArray[i.val]! j.val
  simp only [List.getElem!_toArray]
  exact (check_get as bs wide cs hs h hb hw i.val (by omega) j).symm

theorem check_append (a₁ a₂ bs : List Nat) (wide : List (List Nat))
    (c₁ c₂ : List Nat) (h₁ h₂ : List (Option Nat))
    (p₁ : check a₁ bs wide c₁ h₁ = true) (p₂ : check a₂ bs wide c₂ h₂ = true) :
    check (a₁ ++ a₂) bs wide (c₁ ++ c₂) (h₁ ++ h₂) = true := by
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
end CF
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23
