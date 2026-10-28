module

public import Theory.Representation.PSL3Two.NaturalPlaneStabilizer
public import Theory.SpecificGroups.PSL3Two.Parabolics.LineCore
public import Theory.GroupTheory.PCoreImage

/-!
# The plane radical fixes its plane pointwise

An adapted basis identifies a natural binary plane with the coordinate
plane. The two-core of its stabilizer is the conjugate shear group, which
fixes that plane pointwise. This uses the original natural action.

Source application: Aschbacher–Smith, J.4.2(1), printed p.440.
-/

public section
noncomputable section
open Subgroup Representation Matrix
open scoped Pointwise
namespace BinaryLinearThree.NaturalPlaneStabilizer
open Matrix.PSL3Two

/-- The actual two-core of a plane stabilizer fixes every vector in the plane. -/
theorem core_fixes (A : Submodule (ZMod 2) Vector)
    (hA : Module.finrank (ZMod 2) A = 2)
    (a : Group) (ha : a ∈ (stabilizer A).pCoreIn 2)
    (v : Vector) (hv : v ∈ A) : W a v = v := by
  obtain ⟨g,hg⟩ := exists_matrix A hA
  have hset : (A : Set Vector) = g • (standard : Set Vector) := by
    ext u
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change u ∈ A ↔ W g⁻¹ u ∈ standard
    have h := hg (W g⁻¹ u)
    rwa [Representation.self_inv_apply] at h
  have hs : stabilizer A = lineParabolicSL.map (MulAut.conj g).toMonoidHom := by
    rw [stabilizer_eq,hset,MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    rw [← stabilizer_eq,stabilizer_standard]
  rw [hs,← map_pCoreIn_of_injective 2 lineParabolicSL
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
    lineParabolicSL_pCoreIn_two_eq_R] at ha
  obtain ⟨b,hb,rfl⟩ := ha
  have hu : W g⁻¹ v ∈ standard := by
    have h := hg (W g⁻¹ v)
    rw [Representation.self_inv_apply] at h
    exact h.mp hv
  have hf : W b (W g⁻¹ v) = W g⁻¹ v := by
    obtain ⟨c,rfl⟩ := hb
    rw [mem_standard] at hu
    change !![1,0,c.toAdd.1; 0,1,c.toAdd.2; 0,0,1].mulVec (W g⁻¹ v) = W g⁻¹ v
    ext i
    fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_three,hu]
  change W (g * b * g⁻¹) v = v
  simp only [map_mul,Module.End.mul_apply,hf,Representation.self_inv_apply]

end BinaryLinearThree.NaturalPlaneStabilizer
