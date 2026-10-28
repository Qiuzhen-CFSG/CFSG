module
public import Theory.Representation.OrthogonalFourPlusMatrix.SylowSingularLine
public import Theory.Representation.SL2FourNaturalOrbits.PointCommutator

/-!
# Cubic action on tensor Sylow lines

The diagonal cubic in the first SL₂(4) factor preserves and moves the
standard common Sylow fixed line. Conjugating the Sylow subgroup transports
this action to each common fixed line while keeping the actor in the first
factor. This provides the intrinsic cubic needed for the tensor core argument
in Aschbacher–Smith 9.3.6.
-/

public section
open Matrix Subgroup Representation Representation.BinaryOffender
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
noncomputable section
private theorem point_cubic_action (b : F) :
    action (SL2FourNatural.PointCommutator.cubic,1) (pointMap b) =
      pointMap (QuadraticAlgebra.omega * b) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [action_apply,SL2FourNatural.PointCommutator.cubic,pointMap,
      Matrix.mul_apply,Fin.sum_univ_two]

private theorem point_cubic_moves :
    action (SL2FourNatural.PointCommutator.cubic,1) (pointMap 1) ≠ pointMap 1 := by
  rw [point_cubic_action]
  intro h
  have he := congrArg (fun v : V => v 0 1) h
  have hn : (QuadraticAlgebra.omega : F) ≠ 1 := by decide +kernel
  exact hn (by simpa [pointMap] using he)

private theorem action_mul_apply (a b : G) (v : V) :
    action (a*b) v = action a (action b v) :=
  congrArg (fun f : Module.End (ZMod 2) V => f v) (action.map_mul a b)

/-- A cubic in the first factor preserves and moves every tensor Sylow line. -/
theorem exists_first_cubic_on_sylow_line (P : Sylow 2 G) :
    ∃ a : SL2FourNatural.SL, a ^ 3 = 1 ∧
      (∀ v ∈ fixedSpace action (P : Subgroup G),
        action (a,1) v ∈ fixedSpace action (P : Subgroup G)) ∧
      ∃ v ∈ fixedSpace action (P : Subgroup G), action (a,1) v ≠ v := by
  obtain ⟨g,hg⟩ := sylow_fixedSpace_conjugate_point P
  let c := SL2FourNatural.PointCommutator.cubic
  let a := g.1*c*g.1⁻¹
  have ha3 : a ^ 3 = 1 := by
    change (MulAut.conj g.1 c) ^ 3 = 1
    rw [←map_pow,SL2FourNatural.PointCommutator.cubic_pow_three,map_one]
  have hpair : (a,(1 : SL2FourNatural.SL)) = g*(c,1)*g⁻¹ := by
    apply Prod.ext
    · rfl
    · simp
  have he (v : V) : action (a,1) (action g v) = action g (action (c,1) v) := by
    rw [←action_mul_apply,hpair]
    rw [inv_mul_cancel_right,action_mul_apply]
  refine ⟨a,ha3,?_,?_⟩
  · intro v hv
    rw [hg] at hv ⊢
    obtain ⟨w,⟨b,rfl⟩,rfl⟩ := hv
    rw [he,point_cubic_action]
    exact ⟨_,⟨_,rfl⟩,rfl⟩
  · refine ⟨action g (pointMap 1),?_,?_⟩
    · rw [hg]
      exact ⟨_,⟨1,rfl⟩,rfl⟩
    · rw [he]
      exact fun h => point_cubic_moves ((linearAction g).injective h)
end
end ClassicalOrthogonal.FourPlusMatrix.Binary
