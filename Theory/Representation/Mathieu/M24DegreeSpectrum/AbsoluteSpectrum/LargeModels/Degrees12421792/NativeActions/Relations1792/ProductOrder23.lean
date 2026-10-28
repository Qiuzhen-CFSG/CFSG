module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1792
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.Arithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.Data
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.LowProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.MiddleProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.HighProducts

/-!
# Addition-chain assembly of the literal order-23 equation

Seven complete row-product checks suffice for the original, untransposed ATLAS
matrices. The intermediate exponents are 1, 2, 3, 5, 10, 20 and 23. The first
check identifies the product of the original generators; the last checks every
row against the identity. No generator-order, density, action or abstract
presentation hypothesis is used.

The low, middle and high product certificates discharge all seven numerical
premises, proving the unconditional matrix equation and its application to
source word 2. The conditional assembly remains available independently of the
choice of numerical checker. Source: word 2 of ATLAS M24G1-P1, with the
conventions proved in `Presentation.lean`; see `ProductOrder23/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792
open ProductOrder23 ProductOrder23.Data ProductOrder23.Certificate
open Arithmetic

/-- Full-matrix assembly from the seven explicit numerical product checks. -/
theorem product_order23_of_checks
    (h1 : check firstRows secondRows power1Rows = true)
    (h2 : check power1Rows power1Rows power2Rows = true)
    (h3 : check power2Rows power1Rows power3Rows = true)
    (h5 : check power3Rows power2Rows power5Rows = true)
    (h10 : check power5Rows power5Rows power10Rows = true)
    (h20 : check power10Rows power10Rows power20Rows = true)
    (h23 : check power20Rows power3Rows (identityRows 1792) = true) :
    (Data1792.first * Data1792.second) ^ 23 = 1 := by
  let C := Data1792.first * Data1792.second
  have e1 : decodeRows 1792 power1Rows = C := by
    have hp := product 1792 firstRows secondRows power1Rows
      firstRows_length secondRows_length h1
    rw [decode_firstRows, decode_secondRows] at hp
    exact hp.symm
  have e2 : decodeRows 1792 power2Rows = C ^ 2 := by
    rw [← product 1792 _ _ _ power1Rows_length power1Rows_length h2, e1, pow_two]
  have e3 : decodeRows 1792 power3Rows = C ^ 3 := by
    rw [← product 1792 _ _ _ power2Rows_length power1Rows_length h3, e2, e1]
    exact (pow_succ C 2).symm
  have e5 : decodeRows 1792 power5Rows = C ^ 5 := by
    rw [← product 1792 _ _ _ power3Rows_length power2Rows_length h5, e3, e2]
    exact (pow_add C 3 2).symm
  have e10 : decodeRows 1792 power10Rows = C ^ 10 := by
    rw [← product 1792 _ _ _ power5Rows_length power5Rows_length h10, e5]
    exact (pow_add C 5 5).symm
  have e20 : decodeRows 1792 power20Rows = C ^ 20 := by
    rw [← product 1792 _ _ _ power10Rows_length power10Rows_length h20, e10]
    exact (pow_add C 10 10).symm
  have hp := product 1792 _ _ _ power20Rows_length power3Rows_length h23
  rw [decode_identityRows, e20, e3, ← pow_add] at hp
  exact hp

/-- The complete untransposed degree-1792 product satisfies the order-23 equation. -/
theorem product_order23 : (Data1792.first * Data1792.second) ^ 23 = 1 :=
  product_order23_of_checks LowProducts.base LowProducts.square LowProducts.cube
    MiddleProducts.fifth MiddleProducts.tenth HighProducts.twentieth HighProducts.closing

/-- Discharge source word 2 for the assembly of all seven row relations. -/
theorem product_word2 :
    Presentation.rowRelatorValues Data1792.first Data1792.second 2 = 1 := by
  change (Data1792.first * Data1792.second) ^ 23 = 1
  exact product_order23

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792
