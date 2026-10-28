module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.Data
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.Arithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.HighProducts.Twentieth.Block13
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.HighProducts.Closing.Block13
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.HighProducts.Tables

/-!
# The twentieth power and closing identity product in degree 1792

The two unconditional checks cover all 1792 rows. Literal base-65536
digits are reconstructed by kernel checks, and bounded products are
transported through the proved sequential-XOR soundness theorem.
These discharge h20 and h23 in Relations1792.product_order23_of_checks;
the identification of earlier candidates as powers belongs to that
separate assembly.

Source: ATLAS M24G1-f2r1792B0, word 2 of M24G1-P1.
See `HighProducts/source/README.md` and `ProductOrder23/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.HighProducts

open ProductOrder23.Data ProductOrder23.Certificate Tables

/-- Complete check of all 1792 rows of the twentieth product. -/
theorem twentieth : check power10Rows power10Rows power20Rows = true := by
  have h0 := of_masks _ _ _ right10_length Twentieth.block00
  rw [right10_eq] at h0
  have h1 := of_masks _ _ _ right10_length Twentieth.block01
  rw [right10_eq] at h1
  have h2 := of_masks _ _ _ right10_length Twentieth.block02
  rw [right10_eq] at h2
  have h3 := of_masks _ _ _ right10_length Twentieth.block03
  rw [right10_eq] at h3
  have h4 := of_masks _ _ _ right10_length Twentieth.block04
  rw [right10_eq] at h4
  have h5 := of_masks _ _ _ right10_length Twentieth.block05
  rw [right10_eq] at h5
  have h6 := of_masks _ _ _ right10_length Twentieth.block06
  rw [right10_eq] at h6
  have h7 := of_masks _ _ _ right10_length Twentieth.block07
  rw [right10_eq] at h7
  have h8 := of_masks _ _ _ right10_length Twentieth.block08
  rw [right10_eq] at h8
  have h9 := of_masks _ _ _ right10_length Twentieth.block09
  rw [right10_eq] at h9
  have h10 := of_masks _ _ _ right10_length Twentieth.block10
  rw [right10_eq] at h10
  have h11 := of_masks _ _ _ right10_length Twentieth.block11
  rw [right10_eq] at h11
  have h12 := of_masks _ _ _ right10_length Twentieth.block12
  rw [right10_eq] at h12
  have h13 := of_masks _ _ _ right10_length Twentieth.block13
  rw [right10_eq] at h13
  have hs : List.Forall₂ (fun x z => check x power10Rows z = true) segments10 segments20 :=
    .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7 (.cons h8 (.cons h9 (.cons h10 (.cons h11 (.cons h12 (.cons h13 (.nil))))))))))))))
  have h := flattenChecks _ _ _ hs
  rwa [segments10_eq, segments20_eq] at h

/-- Complete check of all 1792 rows of the closing product. -/
theorem closing : check power20Rows power3Rows (Relations1792.identityRows 1792) = true := by
  have h0 := of_masks _ _ _ right3_length Closing.block00
  rw [right3_eq] at h0
  have h1 := of_masks _ _ _ right3_length Closing.block01
  rw [right3_eq] at h1
  have h2 := of_masks _ _ _ right3_length Closing.block02
  rw [right3_eq] at h2
  have h3 := of_masks _ _ _ right3_length Closing.block03
  rw [right3_eq] at h3
  have h4 := of_masks _ _ _ right3_length Closing.block04
  rw [right3_eq] at h4
  have h5 := of_masks _ _ _ right3_length Closing.block05
  rw [right3_eq] at h5
  have h6 := of_masks _ _ _ right3_length Closing.block06
  rw [right3_eq] at h6
  have h7 := of_masks _ _ _ right3_length Closing.block07
  rw [right3_eq] at h7
  have h8 := of_masks _ _ _ right3_length Closing.block08
  rw [right3_eq] at h8
  have h9 := of_masks _ _ _ right3_length Closing.block09
  rw [right3_eq] at h9
  have h10 := of_masks _ _ _ right3_length Closing.block10
  rw [right3_eq] at h10
  have h11 := of_masks _ _ _ right3_length Closing.block11
  rw [right3_eq] at h11
  have h12 := of_masks _ _ _ right3_length Closing.block12
  rw [right3_eq] at h12
  have h13 := of_masks _ _ _ right3_length Closing.block13
  rw [right3_eq] at h13
  have hs : List.Forall₂ (fun x z => check x power3Rows z = true) segments20 segments23 :=
    .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7 (.cons h8 (.cons h9 (.cons h10 (.cons h11 (.cons h12 (.cons h13 (.nil))))))))))))))
  have h := flattenChecks _ _ _ hs
  rwa [segments20_eq, segments23_eq] at h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.HighProducts
