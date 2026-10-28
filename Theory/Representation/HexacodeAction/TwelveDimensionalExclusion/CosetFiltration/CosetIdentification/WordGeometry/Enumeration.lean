module
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.CosetIdentification.WordGeometry.GroupWords
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.CosetIdentification.WordGeometry.EnumerationChecks
public import Mathlib.Order.Fin.Basic

/-!
# The complete enumeration of the actual cover

Strictly increasing keys prove distinctness of the 1080 sorted products.
Distinctness also forces their slot map to be a permutation. Thus all original
products `z^k r_i p` are distinct; the independently proved order 1080 of the
actual cover makes them exhaustive. Only equality implies equality of matrix
keys; no unproved injectivity of a hash or external coverage claim is used.

Source application: Aschbacher–Smith K.1.3, printed p.453 / PDF p.464.
Witness provenance and ATLAS attribution are recorded in `source/README.md`.
-/

@[expose] public section

open Atlas.Codes
open Representation.Hexacode.SixDimensional.EvenImage.PairData
namespace Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification.WordGeometry

private theorem all_of_blocks {P : Fin 1080 → Prop}
    (h : ∀ b c, P (blockIndex b c)) (n : Fin 1080) : P n := by
  obtain ⟨⟨b,c⟩, rfl⟩ := (finProdFinEquiv : Fin 45 × Fin 24 ≃ Fin 1080).surjective n
  exact h b c

theorem sortedKey_product (n : Fin 1080) :
    matrixKey (productMatrix (sortedIndex n)) = sortedKey n := by
  exact all_of_blocks (P := fun n =>
    matrixKey (productMatrix (sortedIndex n)) = sortedKey n)
    (fun b c => (block_checks b c).1) n

theorem sortedKey_strictMono : StrictMono sortedKey := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact all_of_blocks (P := fun n => ∀ h : n.val + 1 < 1080,
    sortedKey n < sortedKey ⟨n.val + 1,h⟩)
    (fun b c => (block_checks b c).2) i.castSucc i.succ.isLt

theorem sorted_product_injective : Function.Injective (productElement ∘ sortedIndex) := by
  intro a b h
  apply sortedKey_strictMono.injective
  have hm := congrArg coverMatrix h
  simp only [Function.comp_apply, coverMatrix_productElement] at hm
  have hk := congrArg matrixKey (decode_injective hm)
  simpa only [sortedKey_product] using hk

/-- Distinctness of the sorted products also certifies that every slot occurs. -/
theorem sortedIndex_bijective : Function.Bijective sortedIndex := by
  have hi : Function.Injective sortedIndex := fun _ _ h =>
    sorted_product_injective (congrArg productElement h)
  apply hi.bijective_of_nat_card_le
  norm_num [ProductIndex, Nat.card_prod, Nat.card_fin]

theorem productElement_injective : Function.Injective productElement := by
  intro a b h
  obtain ⟨i,rfl⟩ := sortedIndex_bijective.2 a
  obtain ⟨j,rfl⟩ := sortedIndex_bijective.2 b
  exact congrArg sortedIndex (sorted_product_injective h)

/-- The independently proved order of the actual cover turns distinctness into coverage. -/
theorem productElement_bijective : Function.Bijective productElement := by
  apply productElement_injective.bijective_of_nat_card_le
  change Nat.card HexEvenAutomorphisms ≤ Nat.card ProductIndex
  rw [hexEven_card]
  norm_num [ProductIndex, Nat.card_prod, Nat.card_fin]

end Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification.WordGeometry
