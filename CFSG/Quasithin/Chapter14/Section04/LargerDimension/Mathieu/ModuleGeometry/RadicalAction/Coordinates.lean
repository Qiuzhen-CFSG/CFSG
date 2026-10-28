module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.ParabolicCoordinates

/-!
# Binary coordinates adapted to the Mathieu radical

The checked frame has columns 1327, 1047, 1543 and their central cubic
images. A left inverse proves injectivity; its coordinates in the already
certified totally singular six-space identify its range with that literal
space. These coordinates are used for the restricted operator calculations
in Aschbacher–Smith 14.4.12, printed p.1012.

The native ATLAS matrices and attribution are inherited from
`ModuleGeometry.ParabolicCoordinates`. No group-placement assertion is
inferred from the exploratory GAP calculation.
-/

@[expose] public section

open Matrix Representation.SL2FourNatural
open Sporadic.Mathieu M22TripleCover M22TripleCover.Unitary
open M22TripleCover.Uniqueness.PointRestriction (fieldModule fieldTower)
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Representation.BinaryOffender
open scoped Matrix

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.RadicalAction

abbrev Six := Fin 6 → ZMod 2
abbrev MatSix := Matrix (Fin 6) (Fin 6) (ZMod 2)

def binaryRows {m n : ℕ} (rows : Fin m → ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => if (rows i).testBit j.val then 1 else 0

def frame : Matrix (Fin 12) (Fin 6) (ZMod 2) :=
  binaryRows ![39,63,55,49,50,25,48,56,41,28,55,40]

def decoder : Matrix (Fin 6) (Fin 12) (ZMod 2) :=
  binaryRows ![35,59,55,6,5,46]

def coefficients : Matrix (Fin 3) (Fin 6) F :=
  (!![3,3,0,1,1,0; 1,1,3,2,2,1; 2,3,1,3,1,2] : Matrix _ _ ℕ).map fieldEntry

theorem decoder_frame : decoder * frame = 1 := by decide +kernel

theorem frame_coordinates :
    coordMatrix * frame.map (algebraMap (ZMod 2) F) = parabolicMatrix * coefficients := by
  decide +kernel

def embedding : Six →ₗ[ZMod 2] BinarySpace := frame.mulVecLin

theorem embedding_injective : Function.Injective embedding := by
  intro u v h
  have hh := congrArg (fun w => decoder *ᵥ w) h
  simpa only [embedding, mulVecLin_apply, mulVec_mulVec, decoder_frame, one_mulVec] using hh

noncomputable section
local instance : Module F BinarySpace :=
  fieldModule binaryRepresentation binaryRepresentation_faithful
local instance : IsScalarTower (ZMod 2) F BinarySpace :=
  fieldTower binaryRepresentation binaryRepresentation_faithful

theorem embedding_mem_parabolic (u : Six) : embedding u ∈ parabolicSpace := by
  refine ⟨coefficients *ᵥ (fun i => algebraMap (ZMod 2) F (u i)), ?_⟩
  apply coordinates.injective
  rw [coordinates_parabolicEmbedding]
  change _ = coordinateMap (frame *ᵥ u)
  rw [coordinateMap_apply]
  have hlift : binaryLift (frame *ᵥ u) =
      frame.map (algebraMap (ZMod 2) F) *ᵥ (fun i => algebraMap (ZMod 2) F (u i)) := by
    funext i
    exact RingHom.map_mulVec (algebraMap (ZMod 2) F) frame u i
  simp only [hlift, mulVec_mulVec, frame_coordinates]

theorem embedding_range : embedding.range = parabolicSpace := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro v ⟨u, rfl⟩
    exact embedding_mem_parabolic u
  · rw [LinearMap.finrank_range_of_inj embedding_injective, parabolicSpace_finrank]
    simp [Six]

def frameEquiv : Six ≃ₗ[ZMod 2] parabolicSpace :=
  (LinearEquiv.ofInjective embedding embedding_injective).trans
    (LinearEquiv.ofEq _ _ embedding_range)

theorem frameEquiv_val (u : Six) : (frameEquiv u : BinarySpace) = embedding u := rfl

theorem frame_marked : embedding (Pi.single 0 1) = markedVector := by decide +kernel

end
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.RadicalAction
