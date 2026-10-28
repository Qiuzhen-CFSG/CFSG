module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.InnerEstimate.RepresentativeBounds.TensorCoordinates
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Nine independent displacement images for each proper-support involution

For each of the literal matrices I+E₀₁ and (I+E₀₁)(I+E₂₃), nine explicit
SL₄ matrices translate the seed e₀ ⊗ (e₀ ∧ e₁). Coordinate functionals give
a left inverse on their displacement images. The finite identities are checked
by the kernel after reducing seed actions to tensor-matrix columns; no module
catalogue, simplicity certificate, or enumeration of the whole group is used.

Source application: Aschbacher–Smith K.3.2, printed pp.454–455; Guralnick–Malle,
Classification of 2F-modules II, author manuscript Proposition 4.7, pp.25–26.
The tensor action is the actual natural–exterior action from `TensorModel`.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.RepresentativeBounds
open Representation
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
open SupportSeparation
open scoped BigOperators MatrixGroups

/-- The two literal involutions used by the proper-support contract. -/
def representative : Fin 2 → Group := ![simpleUpper 0, simpleUpper 0 * simpleUpper 2]

/-- Nine actual special-linear matrices for each displacement calculation. -/
def translate : Fin 2 → Fin 9 → Group := ![
  ![
    ⟨!![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1], by decide⟩,
    ⟨!![0,0,1,0; 0,1,0,0; 1,0,0,0; 0,0,0,1], by decide⟩,
    ⟨!![0,0,1,0; 0,1,0,0; 0,0,0,1; 1,0,0,0], by decide⟩,
    ⟨!![1,0,1,0; 0,1,0,0; 1,0,0,0; 0,0,0,1], by decide⟩,
    ⟨!![1,0,1,0; 0,1,0,0; 0,0,0,1; 1,0,0,0], by decide⟩,
    ⟨!![0,0,1,0; 1,0,0,0; 0,1,0,0; 0,0,0,1], by decide⟩,
    ⟨!![0,0,1,0; 1,0,0,0; 0,0,0,1; 0,1,0,0], by decide⟩,
    ⟨!![0,0,1,0; 0,1,0,0; 1,0,0,1; 1,0,0,0], by decide⟩,
    ⟨!![0,0,1,0; 1,0,0,1; 1,0,0,0; 0,1,0,0], by decide⟩],
  ![
    ⟨!![1,0,0,0; 0,0,1,0; 0,0,0,1; 0,1,0,0], by decide⟩,
    ⟨!![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1], by decide⟩,
    ⟨!![0,0,1,0; 0,1,0,0; 1,0,0,0; 0,0,0,1], by decide⟩,
    ⟨!![0,0,1,0; 0,0,0,1; 0,1,0,0; 1,0,0,0], by decide⟩,
    ⟨!![0,0,1,0; 1,0,0,0; 0,1,0,0; 0,0,0,1], by decide⟩,
    ⟨!![0,1,0,0; 0,0,1,0; 0,0,0,1; 1,0,0,0], by decide⟩,
    ⟨!![0,0,1,0; 1,0,0,0; 0,1,0,1; 0,1,0,0], by decide⟩,
    ⟨!![0,1,1,0; 0,1,0,0; 0,0,0,1; 1,0,0,0], by decide⟩,
    ⟨!![0,0,1,0; 1,1,0,1; 1,0,0,0; 0,1,0,0], by decide⟩]]

private def coord (p : Fin 4 × Fin 6) : Space →ₗ[ZMod 2] ZMod 2 := LinearMap.proj p

private def extract : Fin 2 → Fin 9 → Space →ₗ[ZMod 2] ZMod 2 := ![
  ![
    coord (0, 0),
    coord (0, 1) + coord (0, 3) + coord (0, 5) + coord (2, 1) + coord (2, 2),
    coord (0, 2) + coord (0, 4) + coord (0, 5) + coord (2, 2) + coord (3, 2),
    coord (0, 1) + coord (0, 3),
    coord (0, 2) + coord (0, 4),
    coord (0, 3),
    coord (0, 4) + coord (0, 5),
    coord (0, 5) + coord (2, 2),
    coord (0, 5)],
  ![
    coord (0, 1) + coord (0, 3),
    coord (0, 0),
    coord (0, 5) + coord (2, 1) + coord (2, 2),
    coord (2, 5),
    coord (0, 3),
    coord (0, 5) + coord (2, 2),
    coord (0, 2) + coord (0, 5),
    coord (0, 5) + coord (2, 3),
    coord (0, 5)]]

private theorem extraction_first (i j : Fin 9) :
    extract 0 i (mixedTensor (representative 0) (mixedTensor (translate 0 j) seed) -
      mixedTensor (translate 0 j) seed) = if j = i then 1 else 0 := by
  rw [← Module.End.mul_apply, ← map_mul, act_seed, act_seed]
  revert i j
  decide

private theorem extraction_second (i j : Fin 9) :
    extract 1 i (mixedTensor (representative 1) (mixedTensor (translate 1 j) seed) -
      mixedTensor (translate 1 j) seed) = if j = i then 1 else 0 := by
  rw [← Module.End.mul_apply, ← map_mul, act_seed, act_seed]
  revert i j
  decide

private theorem extraction (r : Fin 2) (i j : Fin 9) :
    extract r i (mixedTensor (representative r) (mixedTensor (translate r j) seed) -
      mixedTensor (translate r j) seed) = if j = i then 1 else 0 := by
  fin_cases r
  · exact extraction_first i j
  · exact extraction_second i j

/-- Nine independent images under each literal involution, all obtained from
translates of the marked highest vector. -/
theorem independent_displacements (r : Fin 2) :
    LinearIndependent (ZMod 2) (fun j : Fin 9 =>
      mixedTensor (representative r) (mixedTensor (translate r j) seed) -
        mixedTensor (translate r j) seed) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have he := congrArg (extract r i) hc
  simp only [map_sum, map_smul, map_zero, extraction] at he
  simpa [mul_ite] using he

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.RepresentativeBounds
