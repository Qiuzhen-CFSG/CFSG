module

public import Theory.Representation.PSL3Two.NaturalPlaneStabilizer.Core

/-!
# The pointwise fixer of a natural binary plane

A matrix fixing the coordinate plane has its first two columns equal to
those of the identity. Its determinant forces the last diagonal entry to
be one, so it is a shear. An adapted basis transports this calculation to
any two-dimensional subspace. Thus the pointwise fixer is precisely the
two-core of its set stabilizer, for the literal natural action.

Source application: Aschbacher–Smith, J.4.5, printed p.442.
-/

public section
noncomputable section

open Subgroup Representation Matrix
open scoped Pointwise
namespace BinaryLinearThree.NaturalPlaneStabilizer
open Matrix.PSL3Two

private theorem mem_R_of_fixes (a : Group)
    (hf : ∀ v : Vector, v ∈ standard → W a v = v) : a ∈ R := by
  have h0 := hf ![1, 0, 0] (by rw [mem_standard]; simp)
  have h1 := hf ![0, 1, 0] (by rw [mem_standard]; simp)
  have hc0 : ∀ i, a.val i 0 = (![1, 0, 0] : Vector) i := by
    intro i
    simpa [W, specialLinearNatural_apply, SpecialLinearGroup.smul_def, mulVec, dotProduct, Fin.sum_univ_three]
      using congrFun h0 i
  have hc1 : ∀ i, a.val i 1 = (![0, 1, 0] : Vector) i := by
    intro i
    simpa [W, specialLinearNatural_apply, SpecialLinearGroup.smul_def, mulVec, dotProduct, Fin.sum_univ_three]
      using congrFun h1 i
  have h22 : a.val 2 2 = 1 := by
    have hd := a.property
    rw [det_fin_three] at hd
    simpa [hc0, hc1] using hd
  refine ⟨Multiplicative.ofAdd (a.val 0 2, a.val 1 2), ?_⟩
  apply Subtype.ext
  change !![1,0,a.val 0 2; 0,1,a.val 1 2; 0,0,1] = a.val
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc0, hc1, h22]

/-- The pointwise fixer of a binary plane is the actual stabilizer two-core. -/
theorem mem_core_iff_fixes (A : Submodule (ZMod 2) Vector)
    (hA : Module.finrank (ZMod 2) A = 2) (a : Group) :
    a ∈ (stabilizer A).pCoreIn 2 ↔ ∀ v : Vector, v ∈ A → W a v = v := by
  constructor
  · exact core_fixes A hA a
  · intro hf
    obtain ⟨g,hg⟩ := exists_matrix A hA
    have hset : (A : Set Vector) = g • (standard : Set Vector) := by
      ext v
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      change v ∈ A ↔ W g⁻¹ v ∈ standard
      have h := hg (W g⁻¹ v)
      rwa [Representation.self_inv_apply] at h
    have hs : stabilizer A = lineParabolicSL.map (MulAut.conj g).toMonoidHom := by
      rw [stabilizer_eq,hset]
      have he := MulAction.stabilizer_smul_eq_stabilizer_map_conj g (standard : Set Vector)
      rw [← stabilizer_eq standard, stabilizer_standard] at he
      exact he
    rw [hs,← map_pCoreIn_of_injective 2 lineParabolicSL
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
      lineParabolicSL_pCoreIn_two_eq_R]
    refine ⟨g⁻¹ * a * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    apply mem_R_of_fixes
    intro v hv
    have he := hf (W g v) ((hg v).mpr hv)
    change W (g⁻¹ * a * g) v = v
    simp only [map_mul,Module.End.mul_apply,he,Representation.inv_self_apply]

end BinaryLinearThree.NaturalPlaneStabilizer
