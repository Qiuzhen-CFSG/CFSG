module

public import ABG.ChapterII.Section1.WreathedDefs
public import Mathlib.GroupTheory.RegularWreathProduct

/-!
# The height-two presentation of the regular wreath product

The two coordinate generators of C₄ × C₄ and the swapping involution
satisfy ABG's wreathed presentation and generate C₄ ≀ C₂. Coordinate
normal forms prove generation; the wreath cardinality is 32.

Source: Alperin–Brauer–Gorenstein, Chapter II §1, article p.9,
the wreathed presentation preceding Lemma 2.
-/

namespace ABG
namespace RegularWreathHeightTwo

private abbrev C2 := Multiplicative (ZMod 2)
private abbrev C4 := Multiplicative (ZMod 4)
private abbrev W := RegularWreathProduct C4 C2
private abbrev s : W := ⟨fun q => if q = 1 then Multiplicative.ofAdd 1 else 1, 1⟩
private abbrev t : W := ⟨fun q => if q = 1 then 1 else Multiplicative.ofAdd 1, 1⟩
private abbrev z : W := ⟨1, Multiplicative.ofAdd 1⟩

/-- The concrete regular wreath product C₄ ≀ C₂ has ABG height two. -/
public theorem isWreathedOfHeight : ABG.IsWreathedOfHeight
    (RegularWreathProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2))) 2 := by
  refine ⟨by decide, ?_, s, t, z, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [RegularWreathProduct.card]
    norm_num
  · ext q
    · revert q; decide
    · rfl
  · ext q
    · revert q; decide
    · rfl
  · ext q
    · revert q; decide
    · rfl
  · ext q
    · revert q; decide
    · rfl
  · ext q
    · revert q; decide
    · rfl
  · ext q
    · revert q; decide
    · rfl
  · let H := Subgroup.closure ({s, t, z} : Set W)
    have hs : s ∈ H := Subgroup.subset_closure (by simp)
    have ht : t ∈ H := Subgroup.subset_closure (by simp)
    have hz : z ∈ H := Subgroup.subset_closure (by simp)
    apply top_unique
    rintro ⟨f, b⟩ h
    clear h
    have heq : (⟨f, b⟩ : W) = s ^ (f 1).toAdd.val *
        t ^ (f (Multiplicative.ofAdd 1)).toAdd.val * z ^ b.toAdd.val := by
      ext q
      · revert q b f; decide
      · revert b f; decide
    rw [heq]
    exact H.mul_mem (H.mul_mem (H.pow_mem hs _) (H.pow_mem ht _)) (H.pow_mem hz _)

end RegularWreathHeightTwo
end ABG
