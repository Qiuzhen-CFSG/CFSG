module
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry.Completeness
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry.MaskReduction
/-! Two necessary hexad tests for the marked natural-four normalizer.
The masks are hexads 11 and 126 in the Witt-design model. -/
@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair.SylowEnumeration
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def TwoHexadCheck (p : Equiv.Perm (Fin 12)) : Prop :=
  (∃ j : Fin 132, ∀ x : Fin 12,
    (1551 : Nat).testBit (p.symm x).val = (m12BlockMask j).testBit x.val) ∧
  (∃ j : Fin 132, ∀ x : Fin 12,
    (3665 : Nat).testBit (p.symm x).val = (m12BlockMask j).testBit x.val)
noncomputable instance : DecidablePred TwoHexadCheck := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

theorem preserves_twoHexads (p : Equiv.Perm (Fin 12)) (h : PreservesM12Blocks p) :
    TwoHexadCheck p := by
  have h' := (preservesM12Blocks_iff_maskIndexCheck p).mp h
  have h1 : ∃ i : Fin 132, m12BlockMask i = 1551 := by decide +kernel
  have h2 : ∃ i : Fin 132, m12BlockMask i = 3665 := by decide +kernel
  obtain ⟨i,hi⟩ := h1
  obtain ⟨j,hj⟩ := h2
  exact ⟨by simpa only [hi] using h' i, by simpa only [hj] using h' j⟩

end Sporadic.Mathieu.M12SmallPair.SylowEnumeration
