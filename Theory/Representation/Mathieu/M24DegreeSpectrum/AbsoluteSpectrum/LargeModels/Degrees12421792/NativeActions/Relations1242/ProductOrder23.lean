module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.FirstProduct
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.LowPowers
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1242

/-!
# Addition-chain assembly for the degree-1242 product relation

The literal product A B is checked in `FirstProduct`. The six numerical
products certified in `LowPowers`, `MiddlePowers` and `ClosingProducts`
complete the addition chain 1, 2, 3, 5, 10, 13, 23. This module assembles them
into the unconditional order-23 relation and its application to positive ATLAS
word 2, retaining the conditional assembly interfaces as well.

Source: ATLAS M24G1-P1 and M24G1-f2r1242B0.m1/.m2. The original matrices are
untransposed, and multiplication retains the written row-action order.
See `ProductOrder23/source/README.md` for provenance and certificate producers.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242
open ProductOrder23.Tables

/-- Assemble six concrete multiplication certificates. The premises are still
numerical obligations, not assumed source conclusions. -/
theorem product_order23_of_products
    (h2 : c1 * c1 = c2) (h3 : c2 * c1 = c3)
    (h5 : c2 * c3 = c5) (h10 : c5 * c5 = c10)
    (h13 : c10 * c3 = c13) (h23 : c13 * c10 = 1) :
    (Data1242.first * Data1242.second) ^ 23 = 1 := by
  have e2 : c2 = c1 ^ 2 := by rw [← h2, pow_two]
  have e3 : c3 = c1 ^ 3 := by
    calc
      c3 = c2 * c1 := h3.symm
      _ = c1 ^ 2 * c1 := by rw [e2]
      _ = c1 ^ 3 := (pow_succ c1 2).symm
  have e5 : c5 = c1 ^ 5 := by
    calc
      c5 = c2 * c3 := h5.symm
      _ = c1 ^ (2 + 3) := by rw [e2, e3, pow_add]
  have e10 : c10 = c1 ^ 10 := by
    calc
      c10 = c5 * c5 := h10.symm
      _ = c1 ^ (5 + 5) := by rw [e5, pow_add]
  have e13 : c13 = c1 ^ 13 := by
    calc
      c13 = c10 * c3 := h13.symm
      _ = c1 ^ (10 + 3) := by rw [e10, e3, pow_add]
  rw [ProductOrder23.first_product]
  calc
    c1 ^ 23 = c1 ^ 13 * c1 ^ 10 := pow_add c1 13 10
    _ = c13 * c10 := by rw [← e13, ← e10]
    _ = 1 := h23

/-- The same checked products supply the exact positive source word 2. -/
theorem product_word2_of_products
    (h2 : c1 * c1 = c2) (h3 : c2 * c1 = c3)
    (h5 : c2 * c3 = c5) (h10 : c5 * c5 = c10)
    (h13 : c10 * c3 = c13) (h23 : c13 * c10 = 1) :
    Presentation.rowRelatorValues Data1242.first Data1242.second 2 = 1 := by
  change (Data1242.first * Data1242.second) ^ 23 = 1
  exact product_order23_of_products h2 h3 h5 h10 h13 h23

/-- The original untransposed ATLAS generator product satisfies source word 2,
with every numerical multiplication obligation discharged. -/
theorem product_order23 : (Data1242.first * Data1242.second) ^ 23 = 1 :=
  product_order23_of_products
    ProductOrder23.low_square ProductOrder23.low_cube
    ProductOrder23.middle_fifth ProductOrder23.middle_tenth
    ProductOrder23.closing_thirteenth ProductOrder23.closing_identity

/-- The unconditional degree-1242 relation in the literal positive-word family. -/
theorem product_word2 :
    Presentation.rowRelatorValues Data1242.first Data1242.second 2 = 1 := by
  change (Data1242.first * Data1242.second) ^ 23 = 1
  exact product_order23

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242
