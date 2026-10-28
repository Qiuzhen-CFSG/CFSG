module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.RadicalAction.Coordinates

/-!
# Field coordinates and the marked projective line

The adapted binary frame pairs each vector with its central cubic image.
The checked change of basis makes it a genuine F₄-linear frame of the
literal parabolic space. The first two field coordinates give the
projective line through the marked F₄-point. Its vector dimension is two.

Source: Aschbacher–Smith 14.4.12, printed p.1012.
-/

@[expose] public section

open Matrix Representation.SL2FourNatural
open Sporadic.Mathieu M22TripleCover M22TripleCover.Unitary
open M22TripleCover.Uniqueness.PointRestriction (fieldModule fieldTower)
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Representation.BinaryOffender
open scoped Matrix
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.RadicalAction

def fieldSplit : (Fin 3 → F) ≃ₗ[ZMod 2] Six where
  toFun u := ![(u 0).re, (u 1).re, (u 2).re, (u 0).im, (u 1).im, (u 2).im]
  invFun v := ![⟨v 0, v 3⟩, ⟨v 1, v 4⟩, ⟨v 2, v 5⟩]
  left_inv u := by ext i <;> fin_cases i <;> rfl
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' u v := by ext i; fin_cases i <;> rfl
  map_smul' a u := by ext i; fin_cases i <;> rfl

def fieldFrameMatrix : Matrix (Fin 3) (Fin 3) F :=
  (!![3,3,0; 1,1,3; 2,3,1] : Matrix _ _ ℕ).map fieldEntry

def fieldFrameInverse : Matrix (Fin 3) (Fin 3) F :=
  (!![2,2,1; 0,2,1; 3,2,0] : Matrix _ _ ℕ).map fieldEntry

theorem fieldFrame_leftInverse : fieldFrameInverse * fieldFrameMatrix = 1 := by decide +kernel
theorem fieldFrame_rightInverse : fieldFrameMatrix * fieldFrameInverse = 1 := by decide +kernel

noncomputable section
local instance : Module F BinarySpace :=
  fieldModule binaryRepresentation binaryRepresentation_faithful
local instance : IsScalarTower (ZMod 2) F BinarySpace :=
  fieldTower binaryRepresentation binaryRepresentation_faithful

def fieldEmbedding : (Fin 3 → F) →ₗ[F] BinarySpace :=
  parabolicEmbedding.comp fieldFrameMatrix.mulVecLin

def fieldFrame : (Fin 3 → F) ≃ₗ[F] parabolicFieldSpace :=
  LinearEquiv.ofBijective
    (fieldEmbedding.codRestrict parabolicFieldSpace (fun u => ⟨fieldFrameMatrix *ᵥ u, rfl⟩)) (by
      constructor
      · intro u v h
        have he := parabolicEmbedding_injective (congrArg Subtype.val h)
        have hh := congrArg (fun w => fieldFrameInverse *ᵥ w) he
        simpa only [mulVecLin_apply, mulVec_mulVec, fieldFrame_leftInverse, one_mulVec] using hh
      · rintro ⟨v, ⟨u, rfl⟩⟩
        refine ⟨fieldFrameInverse *ᵥ u, ?_⟩
        apply Subtype.ext
        change parabolicEmbedding (fieldFrameMatrix *ᵥ (fieldFrameInverse *ᵥ u)) = _
        rw [mulVec_mulVec, fieldFrame_rightInverse, one_mulVec])

theorem fieldFrame_val (u : Fin 3 → F) : (fieldFrame u : BinarySpace) = fieldEmbedding u := rfl

private def scalarLiftSix : Six →ₗ[ZMod 2] (Fin 6 → F) where
  toFun v i := algebraMap (ZMod 2) F (v i)
  map_add' v w := by funext i; exact map_add _ _ _
  map_smul' a v := by funext i; simp [Algebra.smul_def]

private theorem split_coefficients (u : Fin 3 → F) :
    coefficients *ᵥ scalarLiftSix (fieldSplit u) = fieldFrameMatrix *ᵥ u := by
  have he : ((coefficients.mulVecLin.restrictScalars (ZMod 2)).comp
      (scalarLiftSix.comp fieldSplit.toLinearMap)) =
      fieldFrameMatrix.mulVecLin.restrictScalars (ZMod 2) := by
    apply LinearMap.pi_ext
    have h : ∀ (i : Fin 3) (a : F),
        coefficients *ᵥ scalarLiftSix (fieldSplit (Pi.single i a)) =
          fieldFrameMatrix *ᵥ Pi.single i a := by decide +kernel
    exact h
  exact LinearMap.congr_fun he u

theorem frameEquiv_fieldSplit (u : Fin 3 → F) :
    frameEquiv (fieldSplit u) = (fieldFrame u : parabolicFieldSpace) := by
  apply Subtype.ext
  apply coordinates.injective
  change coordinateMap (frame *ᵥ fieldSplit u) =
    coordinates (parabolicEmbedding (fieldFrameMatrix *ᵥ u))
  rw [coordinates_parabolicEmbedding, coordinateMap_apply]
  have hl : binaryLift (frame *ᵥ fieldSplit u) =
      frame.map (algebraMap (ZMod 2) F) *ᵥ scalarLiftSix (fieldSplit u) := by
    funext i
    exact RingHom.map_mulVec (algebraMap (ZMod 2) F) frame (fieldSplit u) i
  rw [hl]
  simp only [mulVec_mulVec, frame_coordinates]
  rw [← mulVec_mulVec, split_coefficients, mulVec_mulVec]

def fieldLineEmbedding : (Fin 2 → F) →ₗ[F] BinarySpace :=
  fieldEmbedding.comp ((!![1,0; 0,1; 0,0] : Matrix (Fin 3) (Fin 2) F).mulVecLin)

def fieldLine : Submodule F BinarySpace := fieldLineEmbedding.range

theorem fieldLineEmbedding_injective : Function.Injective fieldLineEmbedding := by
  intro u v h
  have he := parabolicEmbedding_injective h
  have hh := congrArg (fun w => fieldFrameInverse *ᵥ w) he
  simp only [mulVecLin_apply, mulVec_mulVec, ← Matrix.mul_assoc,
    fieldFrame_leftInverse] at hh
  funext i
  fin_cases i
  · simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun hh 0
  · simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun hh 1

theorem fieldLine_finrank : Module.finrank F fieldLine = 2 := by
  rw [fieldLine, LinearMap.finrank_range_of_inj fieldLineEmbedding_injective]
  simp

theorem fieldFrame_first : (fieldFrame (Pi.single 0 1) : BinarySpace) = markedVector := by
  rw [← frameEquiv_fieldSplit]
  have he : fieldSplit (Pi.single 0 (1 : F)) = Pi.single 0 1 := by decide +kernel
  rw [he]
  exact frame_marked

theorem markedPoint_le_fieldLine : fieldPoint markedVector ≤ fieldLine := by
  apply Submodule.span_le.mpr
  intro v hv
  rw [Set.mem_singleton_iff.mp hv]
  refine ⟨![1,0], ?_⟩
  have he : fieldLineEmbedding ![1,0] = (fieldFrame (Pi.single 0 1) : BinarySpace) := by
    change parabolicEmbedding (fieldFrameMatrix *ᵥ _) =
      parabolicEmbedding (fieldFrameMatrix *ᵥ Pi.single 0 1)
    apply congrArg parabolicEmbedding
    apply congrArg (fun u => fieldFrameMatrix *ᵥ u)
    decide +kernel
  exact he.trans fieldFrame_first

theorem fieldLine_le_parabolic : fieldLine ≤ parabolicFieldSpace := by
  rintro v ⟨u, rfl⟩
  exact ⟨_, rfl⟩

end
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.RadicalAction
