module

public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.Frame.Inverse
public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.OrbitData

/-!
# The literal 29-line Rudvalis frame

The invertible matrix from `Inverse` has precisely the first 28 published
line vectors as columns. The published line 658 is its product with the
supplied coordinate vector, all of whose entries are nonzero. Thus these
certificates apply to the actual `lineVector` table, independently of any
orbit-equivariance assertion.

Source: ATLAS `2RuG1-f5r28B0`, with witnesses from
`DoubleCover/source/frame.json`; see `Frame/source/README.md`.
-/

namespace Rudvalis.Multiplier.DoubleCover.Frame
public section

/-- Identification with the literal published lines, with the column convention. -/
theorem basis_column : ∀ j : Fin 28, (fun i => basisMatrix i j) =
    lineVector ⟨j.val, by omega⟩ := by decide +kernel

/-- Every coefficient of the additional line in this basis is nonzero. -/
theorem coordinates_ne_zero : ∀ j, coordinates j ≠ 0 := by decide +kernel

/-- The supplied dense coordinates give exactly published line 658. -/
theorem basis_mulVec_coordinates : basisMatrix.mulVec coordinates = lineVector 658 := by
  have h : ∀ i : Fin 28,
      dotNat (entryNat basisMatrixPacked i.val) (entryNat coordinatesPacked 0) 28 % 5 =
      (((lineBlocks[5]!)[18]! >>> (3 * i.val)) % 8) % 5 := by decide +kernel
  funext i
  have hc := congrArg (fun n : ℕ => (n : ZMod 5)) (h i)
  simp only [ZMod.natCast_mod] at hc
  change (∑ k : Fin 28, (entryNat basisMatrixPacked i.val k.val : ZMod 5) *
    (entryNat coordinatesPacked 0 k.val : ZMod 5)) = _
  rw [← dotNat_cast]
  exact hc

end
end Rudvalis.Multiplier.DoubleCover.Frame
