module
public import Theory.Representation.BinaryTensorThree.PointFlag
public import Theory.Representation.BinaryTensorThree.PlaneFixed

/-!
# Cubic movement on the lower tensor point layer

An explicit order-three Levi matrix fixes the original pure-tensor point
and moves one row vector outside its line. This witnesses nontrivial
movement of the five-space modulo the point by the point-parabolic
 two-residual. The source application lifts this same element to X.
Source: Aschbacher--Smith H.4.9(2) and 8.3.12, printed pp.383,726.
-/

public noncomputable section
namespace BinaryTensorThree.PointFlag
open Subgroup Matrix.PSL3Two
open scoped TensorProduct
private def lowerCubicMatrix : SL := ⟨!![1,0,0;0,0,1;0,1,1],by decide +kernel⟩
private def lowerCubic : PointParabolic.PairP :=
  ⟨PlaneFixed.pair (lowerCubicMatrix,1),by
    intro i
    change (if i = 1 then lowerCubicMatrix else 1) ∈ pointParabolicSL
    split
    · decide +kernel
    · exact one_mem _⟩

/-- A cubic in the literal point parabolic moves the five-space modulo the point line. -/
theorem exists_cubic_moving_lower :
    ∃ a : PointParabolic.PairP, a^3 = 1 ∧
      ∃ v ∈ five, action (PointParabolic.tensorHom a) v - v ∉ line := by
  refine ⟨lowerCubic,?_,leftProbe 0,?_,?_⟩
  · apply Subtype.ext
    change (PlaneFixed.pair (lowerCubicMatrix,1))^3 = 1
    rw [←map_pow,show (lowerCubicMatrix,(1:SL))^3 = 1 from by decide +kernel,map_one]
  · intro i j hi hj
    simp [leftProbe,coordinates_tmul,basisVector,hj]
  · have he : action (PointParabolic.tensorHom lowerCubic) (leftProbe 0) = leftProbe 1 := by
      rw [show (lowerCubic : PointParabolic.Actor) = PlaneFixed.pair (lowerCubicMatrix,1) from rfl,
        PlaneFixed.tensor_pair,action_baseEmbedding]
      unfold leftProbe
      rw [baseAction_tmul]
      have hl : Matrix.SpecialLinearGroup.toLin' lowerCubicMatrix (basisVector 1) = basisVector 2 := by
        ext i
        change (lowerCubicMatrix.val.mulVec (basisVector 1)) i = basisVector 2 i
        fin_cases i <;>
          norm_num [lowerCubicMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three,basisVector,
            Pi.single_apply,Fin.ext_iff]
      have hr : Matrix.SpecialLinearGroup.toLin' (1 : SL) (basisVector 0) = basisVector 0 := by
        rw [map_one]
        rfl
      change coordinates (Matrix.SpecialLinearGroup.toLin' lowerCubicMatrix (basisVector 1) ⊗ₜ[ZMod 2]
        Matrix.SpecialLinearGroup.toLin' (1 : SL) (basisVector 0)) = _
      rw [hl,hr]
      rfl

    rw [he]
    intro h
    have hh := h 1 0 (Or.inl (by decide))
    norm_num [leftProbe,coordinates_tmul,basisVector,Pi.single_apply,Fin.ext_iff] at hh
end BinaryTensorThree.PointFlag
