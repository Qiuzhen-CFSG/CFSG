module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.LiteralProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RowArithmetic

/-!
# Sequential checks for the order-23 addition chain

The existing binary XOR checker is independent of the dimension. This module
adapts its complete-list soundness theorem to `Relations1792.decodeRows`.
Small independently checked blocks concatenate, so certificate producers can
bound the size of each kernel reduction. No row is omitted by the adapter.
The concrete consumer is `ProductOrder23.product_order23_of_checks`.

Source: ATLAS M24G1-P1, word 2; see `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.Certificate

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels

/-- Sequential XOR checker, skipping the zero coefficients. -/
abbrev check := Degree320Pair.MatrixCertificates.checkSkip

/-- Checking every stored row proves the full matrix product. -/
theorem product (n : Nat) (xs ys zs : List Nat)
    (hx : xs.length = n) (hy : ys.length = n)
    (h : check xs ys zs = true) :
    Arithmetic.decodeRows n xs * Arithmetic.decodeRows n ys =
      Arithmetic.decodeRows n zs := by
  have hp := Degree320Pair.product_sound_list n xs ys zs hx hy
    (Degree320Pair.MatrixCertificates.checkRows_of_skip xs ys zs h)
  simpa only [← Arithmetic.decodeRows_array, List.toList_toArray] using hp

/-- Concatenate two complete row blocks. -/
theorem append (xs₁ xs₂ ys zs₁ zs₂ : List Nat)
    (h₁ : check xs₁ ys zs₁ = true) (h₂ : check xs₂ ys zs₂ = true) :
    check (xs₁ ++ xs₂) ys (zs₁ ++ zs₂) = true := by
  simpa only [check, Degree320Pair.MatrixCertificates.checkSkip_eq] using
    Degree320Pair.MatrixCertificates.checkRows_append xs₁ xs₂ ys zs₁ zs₂
      (Degree320Pair.MatrixCertificates.checkRows_of_skip _ _ _ h₁)
      (Degree320Pair.MatrixCertificates.checkRows_of_skip _ _ _ h₂)

/-- A finite cut divides a product certificate without changing its meaning. -/
theorem split (xs ys zs : List Nat) (k : Nat)
    (h₁ : check (xs.take k) ys (zs.take k) = true)
    (h₂ : check (xs.drop k) ys (zs.drop k) = true) : check xs ys zs = true := by
  simpa only [List.take_append_drop] using
    append (xs.take k) (xs.drop k) ys (zs.take k) (zs.drop k) h₁ h₂

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.Certificate
