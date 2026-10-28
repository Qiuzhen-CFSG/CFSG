module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.MatrixGenerators

/-!
# Generation of the literal matrix group by the two ATLAS generators

The first generator is the transvection centered at e₀. A checked orbit
of length 63 puts every nonzero vector in its orbit under the two generators.
Conjugating this transvection therefore produces all binary transvections;
the existing symplectic generation theorem gives the full matrix group.

The orbit words were obtained by breadth-first search from the explicit
matrices in `MatrixGenerators`; each word is independently checked here.
This proves surjectivity of the sourced presentation, without presuming
its faithfulness or the value of its Schur multiplier.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation
open Matrix.PSp4Three

abbrev BinaryVector := Coordinate → ZMod 2

def vectorLabel (i : Fin 63) : BinaryVector :=
  fun j => if Nat.testBit (i.val + 1) (coordinate j).val then 1 else 0

private def orbitWord : Fin 63 → List Bool :=
  ![
    [],
    [true, true, true, false, true],
    [true, true, true, true, true, false, true, false, true, true, false, true],
    [true, true, false, true, true, true],
    [true, false, true, true, true, false, true, true, false, true, true, true, true],
    [true, false, true, true, true, true, true, false, true],
    [true, true, true, true, false, true, false, true, true, false, true, true, false, true],
    [true, false, true, false, true, true, false, true, true, false, true],
    [false, true, false, true, false, true, true, false, true, true, false, true],
    [true, true, true, true, false, true],
    [false, true, true, true, true, false, true],
    [true, true, false, true],
    [false, true, true, false, true],
    [false, true, false, true, true, false, true, true, false, true],
    [true, false, true, true, false, true, true, false, true],
    [true, true, true, true, false, true, false, true, true, false, true],
    [true, true, true, true, true, true, false, true, false, true, true, false, true],
    [true, true, true, false, true, true, false, true, true, false, true],
    [true, true, false, true, true, false, true, true, false, true],
    [true, true, true, false, true, true, false, true],
    [true, true, false, true, true, false, true, true, true, true],
    [true, true, true, true, false, true, false, true],
    [true, false, true, false, true],
    [false, true, false, true, true, false, true],
    [true, false, true, true, false, true],
    [false, true],
    [true],
    [true, true, true, true, true, true],
    [false, true, true, true, true, true, true],
    [false, true, true, true, false, true, false, true, true, false, true],
    [true, true, true, false, true, false, true, true, false, true],
    [true, true, true, false, true, true, true],
    [true, false, true, false, true, true, false, true],
    [true, true, false, true, false, true, true, false, true, true, false, true],
    [true, true, true, true, false, true, true, false, true],
    [true, true, false, true, false, true, true, false, true],
    [true, false, true, true, true],
    [true, false, true, true, false, true, true, true, true],
    [true, true, true, true, true, true, false, true, false, true, true, false, true, true, false, true],
    [true, true, true, true, true, false, true],
    [false, true, true, true, true, true, false, true],
    [false, true, false, true],
    [true, false, true],
    [true, true, false, true, true, true, true],
    [false, true, true, false, true, true, true, true],
    [false, true, false, true, true, true, true],
    [true, false, true, true, true, true],
    [true, true],
    [true, true, true, true, true, false, true, false, true, true, false, true, true, false, true],
    [true, true, false, true, false, true],
    [true, false, true, true, true, true, false, true],
    [true, true, true, true, true],
    [true, true, true, false, true, false, true, true, false, true, true, false, true],
    [true, true, true, false, true, false, true],
    [true, false, true, false, true, true, true, true],
    [true, true, true, false, true, true, false, true, true, true, true],
    [false, true, true, true, false, true, true, false, true, true, true, true],
    [true, true, false, true, true, false, true],
    [false, true, true, false, true, true, false, true],
    [true, true, true],
    [false, true, true, true],
    [true, true, true, true],
    [false, true, true, true, true]
]

private def wordAction : List Bool → BinaryVector
  | [] => Matrix.PSp4Three.e 0
  | i :: w => matrixGenerator i • wordAction w

private theorem orbitWord_correct (i : Fin 63) : wordAction (orbitWord i) = vectorLabel i := by
  revert i
  decide +kernel

private theorem vectorLabel_surjective :
    ∀ v : BinaryVector, v ≠ 0 → ∃ i : Fin 63, vectorLabel i = v := by
  decide +kernel

private def wordValue (w : List Bool) : Base := (w.map matrixGenerator).prod

private theorem wordValue_action (w : List Bool) : wordValue w • Matrix.PSp4Three.e 0 = wordAction w := by
  induction w with
  | nil => simp [wordValue, wordAction]
  | cons i w ih => simpa [wordValue, wordAction, mul_smul] using congrArg (fun v => matrixGenerator i • v) ih

private theorem wordValue_mem_range (w : List Bool) : wordValue w ∈ matrixMap.range := by
  induction w with
  | nil => exact matrixMap.range.one_mem
  | cons i w ih =>
    exact matrixMap.range.mul_mem ⟨generator i, matrixMap_generator i⟩ ih

theorem a_eq_transvection : a = transvection (Matrix.PSp4Three.e (n := 3) (F := ZMod 2) 0) 1 := by
  apply Subtype.ext
  decide +kernel

/-- All nonzero transvection centers occur in the actual generated group. -/
theorem exists_matrixMap_range_send (v : BinaryVector) (hv : v ≠ 0) :
    ∃ g ∈ matrixMap.range, g • Matrix.PSp4Three.e 0 = v := by
  obtain ⟨i, rfl⟩ := vectorLabel_surjective v hv
  exact ⟨wordValue (orbitWord i), wordValue_mem_range _,
    (wordValue_action _).trans (orbitWord_correct i)⟩

/-- The presentation maps onto the literal Sp₆(2), by transvection generation. -/
theorem matrixMap_surjective : Function.Surjective matrixMap := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← transvectionGroup_eq_top (n := 3) (F := ZMod 2)]
  unfold transvectionGroup
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨v, c, rfl⟩
  have hc : c = 0 ∨ c = 1 := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
  rcases hc with rfl | rfl
  · rw [transvection_zero]
    exact matrixMap.range.one_mem
  by_cases hv : v = 0
  · rw [hv, transvection_zero_vector]
    exact matrixMap.range.one_mem
  obtain ⟨g, hg, hgv⟩ := exists_matrixMap_range_send v hv
  rw [← hgv, ← transvection_conjugate, ← a_eq_transvection]
  exact matrixMap.range.mul_mem
    (matrixMap.range.mul_mem hg ⟨generator false, matrixMap_generator false⟩)
    (matrixMap.range.inv_mem hg)

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation
