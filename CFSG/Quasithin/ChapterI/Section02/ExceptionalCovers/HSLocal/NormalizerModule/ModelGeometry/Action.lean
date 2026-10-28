module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.ModelGeometry.Core
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.CoreGeometry.Action

/-!
# The normalizer action inputs to the HS double-cover argument

The actual model normalizer is perfect and has odd index. An order-seven
element has trivial centralizer in the embedded core A. These are the model
premises used for perfectness and coprime splitting upstairs; this module
makes no assertion about a covering group or a noncentral lift.

Source: Aschbacher–Smith I.2.2(5), printed p.412 / PDF p.423.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.ModelGeometry
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.BlockNormalizer

/-- The source's model perfectness premise is unconditional for this normalizer. -/
theorem normalizer_perfect : Group.IsPerfect baseNormalizer :=
  CoreGeometry.normalizer_isPerfect

theorem normalizer_odd_index : Odd baseNormalizer.index := CoreGeometry.normalizer_odd_index

/-- The literal ambient form of the fixed-free model action needed for coprime splitting. -/
theorem exists_seven_centralizer_trivial : ∃ y : baseNormalizer, orderOf y = 7 ∧
    ∀ a ∈ A, Commute (y : Carrier) a → a = 1 := by
  obtain ⟨y, hy, hfree⟩ := CoreGeometry.exists_seven_fixedPointFree
  refine ⟨y, hy, ?_⟩
  rintro a ⟨b, hb, rfl⟩ hc
  change Commute (y : Carrier) (b : Carrier) at hc
  have he := hfree (⟨b, hb⟩ : pCore 2 baseNormalizer) (by
    apply Subtype.ext
    apply Subtype.ext
    change (y : Carrier) * (b : Carrier) * (y : Carrier)⁻¹ = (b : Carrier)
    rw [hc.eq, mul_inv_cancel_right])
  exact congrArg (fun q : pCore 2 baseNormalizer => (q.val : Carrier)) he

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.ModelGeometry
