module
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry.TwoHexads
/-! Integer encoding of the two necessary hexad tests. Summing the twelve
binary digits once avoids repeated evaluation for every possible target hexad. -/
@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair.SylowEnumeration
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def bitsCode (f : Fin 12 → Bool) : Nat :=
  ∑ x : Fin 12, if f x then 2 ^ x.val else 0

noncomputable def blockCodes : List Nat := List.ofFn m12BlockMask

theorem block_bitsCode : ∀ j : Fin 132,
    bitsCode (fun x => (m12BlockMask j).testBit x.val) = m12BlockMask j := by
  decide +kernel

noncomputable def FastHexadCheck (p : Equiv.Perm (Fin 12)) : Prop :=
  bitsCode (fun x => (1551 : Nat).testBit (p.symm x).val) ∈ blockCodes ∧
  bitsCode (fun x => (3665 : Nat).testBit (p.symm x).val) ∈ blockCodes
noncomputable instance : DecidablePred FastHexadCheck := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

theorem twoHexadCheck_fast (p : Equiv.Perm (Fin 12)) (h : TwoHexadCheck p) :
    FastHexadCheck p := by
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := h
  have hi' := congrArg bitsCode (funext hi)
  have hj' := congrArg bitsCode (funext hj)
  rw [block_bitsCode] at hi' hj'
  constructor
  · rw [hi']
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · rw [hj']
    exact List.mem_ofFn.mpr ⟨j,rfl⟩
end Sporadic.Mathieu.M12SmallPair.SylowEnumeration
