/-
The Golay basis and marked Leech coordinates are those of Gerald Höhn,
ATLAS revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
See LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechForm

/-! The explicit coordinate bijection for the McLaughlin matrix certificates.
This is the ATLAS Golay coordinate order: four entries in each of six columns. -/

@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
open Atlas.Codes Atlas.Lattices
open scoped Matrix BigOperators
/-- The coordinate order used by the supplied 24 by 24 matrices. -/
def coordinate (i : Fin 24) : Omega := ![((0, 0), 0), ((0, 0), 1), ((0, 0), 2), ((0, 0), 3), ((0, 1), 0), ((0, 1), 1), ((0, 1), 2), ((0, 1), 3), ((1, 0), 0), ((1, 0), 1), ((1, 0), 2), ((1, 0), 3), ((1, 1), 0), ((1, 1), 1), ((1, 1), 2), ((1, 1), 3), ((2, 0), 0), ((2, 0), 1), ((2, 0), 2), ((2, 0), 3), ((2, 1), 0), ((2, 1), 1), ((2, 1), 2), ((2, 1), 3)] i

theorem coordinate_injective : Function.Injective coordinate := by
  have h : ∀ i j : Fin 24, coordinate i = coordinate j → i = j := by decide +kernel
  exact h

def coordinateIndex (i : Omega) : Fin 24 :=
  ⟨8 * i.1.1.val + 4 * i.1.2.val + i.2.val, by
    have h1 := i.1.1.isLt
    have h2 := i.1.2.isLt
    have h3 := i.2.isLt
    omega⟩

theorem coordinateIndex_apply (i : Omega) : coordinate (coordinateIndex i) = i := by
  fin_cases i <;> rfl

theorem coordinateIndex_coordinate (j : Fin 24) : coordinateIndex (coordinate j) = j := by
  fin_cases j <;> rfl

def reindex : (Fin 24 → ℚ) ≃ₗ[ℚ] (Omega → ℚ) where
  toFun x i := x (coordinateIndex i)
  invFun x j := x (coordinate j)
  left_inv x := by
    funext j
    change x (coordinateIndex (coordinate j)) = x j
    rw [coordinateIndex_coordinate]
  right_inv x := by
    funext i
    change x (coordinate (coordinateIndex i)) = x i
    rw [coordinateIndex_apply]
  map_add' x y := by rfl
  map_smul' r x := by rfl

def vectorOfData (v : Fin 24 → ℤ) : IntegerCoordinates := fun i => v (coordinateIndex i)

def rationalVectorOfData (v : Fin 24 → ℚ) : RationalCoordinates := fun i => v (coordinateIndex i)


end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
