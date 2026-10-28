module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders.Checker

/-!
# Boolean certificates for the five fixed cube products

The checker evaluates each row once and the soundness lemma recovers the
ordinary mapped-list equality. The existing proved carry-free algorithm then
identifies this equality with multiplication of the original binary matrices.
Source: ATLAS M24G1-P1; see `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders

/-- Checked pointwise evaluation, with no trusted numerical witness. -/
def checkMap (f : Nat → Nat) : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, c :: cs => (f a == c) && checkMap f as cs
  | _, _ => false

theorem checkMap_sound (f : Nat → Nat) (as cs : List Nat)
    (h : checkMap f as cs = true) : as.map f = cs := by
  induction as generalizing cs with
  | nil => cases cs <;> simp_all [checkMap]
  | cons a as ih =>
    cases cs with
    | nil => simp [checkMap] at h
    | cons c cs =>
      simp only [checkMap, Bool.and_eq_true, beq_iff_eq] at h
      exact congrArg₂ List.cons h.1 (ih cs h.2)

theorem checkMap_cons (f : Nat → Nat) (a c : Nat) (as cs : List Nat)
    (ha : f a = c) (hs : checkMap f as cs = true) :
    checkMap f (a :: as) (c :: cs) = true := by
  simp only [checkMap, Bool.and_eq_true, beq_iff_eq]
  exact ⟨ha, hs⟩

theorem checkMap_append (f : Nat → Nat) (as bs cs ds : List Nat)
    (h₁ : checkMap f as cs = true) (h₂ : checkMap f bs ds = true) :
    checkMap f (as ++ bs) (cs ++ ds) = true := by
  induction as generalizing cs with
  | nil => cases cs <;> simp_all [checkMap]
  | cons a as ih =>
    cases cs with
    | nil => simp [checkMap] at h₁
    | cons c cs =>
      simp only [checkMap, Bool.and_eq_true] at h₁
      simp only [List.cons_append, checkMap, Bool.and_eq_true]
      exact ⟨h₁.1, ih cs h₁.2⟩

/-- Numerical row checks, including the widened-table bridge, certify an
actual product of the fixed binary decoder. -/
theorem checked_product (xs ys zs : List Nat) (wide : List (List Nat))
    (hx : xs.length = 1242) (hy : ys.length = 1242)
    (hw : wide.flatten = ys.map (expandTree 6 1242))
    (hc : checkMap (fun a => compressTree 6 1242 (accumChunks a wide)) xs zs = true) :
    Thompson.BinaryMatrix.decode 1242 xs.toArray *
        Thompson.BinaryMatrix.decode 1242 ys.toArray =
      Thompson.BinaryMatrix.decode 1242 zs.toArray := by
  have he : expandTree 6 1242 = expand 1242 := funext (expandTree_eq 6 1242)
  have hw' : wide.flatten = ys.map (expand 1242) := by simpa only [he] using hw
  have hc' := checkMap_sound _ _ _ hc
  simp only [compressTree_eq, accumChunks_eq] at hc'
  have h := product_sound 1242 (by decide) xs ys zs wide.flatten hx hy hw' hc'
  have bridge (ls : List Nat) : decodeRows 1242 ls =
      Thompson.BinaryMatrix.decode 1242 ls.toArray := by
    simpa only [List.toList_toArray] using decodeRows_array 1242 ls.toArray
  simpa only [bridge] using h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts
