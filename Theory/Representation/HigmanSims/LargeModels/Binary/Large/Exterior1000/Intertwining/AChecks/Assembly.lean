module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining.Tables
public import Theory.Representation.HigmanSims.LargeModels.Binary.Data1000

/-!
# Assembly of first-generator exterior-section certificates

The individual obligations are the literal packed products for the degree-1000
section. Splitting a finite interval lets the complete family reuse independently
kernel-checked batches without reducing their arithmetic again.

Source: R. A. Wilson et al., ATLAS HSG1-f2r56B0/HSG1-f2r1000B0 and
`Binary/source/section1000.json`. See `Binary/source/README.md` for attribution
and rights. Original repository code under Apache 2.0.
-/

namespace Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining.AChecks

/-- The literal first-generator product obligation at one natural-number index. -/
@[expose] public def Row (i : ℕ) : Prop :=
  Tables.a.product liftRows[i]! = Tables.lifts.product D1000.aRows[i]!

/-- Concatenate two adjacent certified ranges. -/
public theorem appendRange (start left right : ℕ)
    (hl : ∀ i : Fin left, Row (start + i.val))
    (hr : ∀ i : Fin right, Row (start + left + i.val)) :
    ∀ i : Fin (left + right), Row (start + i.val) := by
  intro i
  by_cases h : i.val < left
  · exact hl ⟨i.val, h⟩
  · have hi : i.val - left < right := by omega
    have e : start + left + (i.val - left) = start + i.val := by omega
    exact e ▸ hr ⟨i.val - left, hi⟩

end Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining.AChecks
