module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Models
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Intrinsic binary linear actor facts

Elementary transvections show that the natural binary linear action is generated
by displacements and has zero fixed space. The genuine PSL-to-linear equivalence
transfers simplicity in dimension at least three. In dimension two, the actual
SL₂(2)-to-S₃ equivalence proves solvability, excluding this case for a nonsolvable
actor.

Source application: Aschbacher–Smith G.6.4(2a), printed pp.345–346, and the
component section in 13.8.5, p.947. The imported PSL simplicity proof is the
attributed ATLAS port in `Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity`.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep.ModelComponents
open Subgroup Representation Representation.BinaryOffender
open BinaryLinear BinaryLinear.OuterCyclic

/-- Elementary transvections generate every vector as a displacement. -/
theorem linear_generated (n : ℕ) (hn : 2 ≤ n) :
    subspaceCommutator (linearRepresentation n) ⊤ ⊤ = ⊤ := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  let W := subspaceCommutator (linearRepresentation n) ⊤ ⊤
  have hs (i : Fin n) : Pi.single i (1 : ZMod 2) ∈ W := by
    obtain ⟨j, hji⟩ := exists_ne i
    let f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := LinearMap.proj j
    have hf : f (Pi.single i 1) = 0 := by simp [f, hji]
    let g := transvection (Pi.single i 1) f hf
    have h : linearRepresentation n g (Pi.single j 1) - Pi.single j 1 ∈ W :=
      Submodule.subset_span ⟨g, mem_top _, Pi.single j 1, Submodule.mem_top, rfl⟩
    let x : Fin n → ZMod 2 := Pi.single j 1
    change (x + x j • Pi.single i 1) - x ∈ W at h
    simpa [x] using h
  apply top_unique
  intro v _
  rw [← Finset.univ_sum_single v]
  apply W.sum_mem
  intro i _
  have h := W.smul_mem (v i) (hs i)
  simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using h

/-- Elementary transvections force every fixed coordinate to vanish. -/
theorem linear_fixed (n : ℕ) (hn : 2 ≤ n) :
    fixedSpace (linearRepresentation n) ⊤ = ⊥ := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  apply eq_bot_iff.mpr
  intro v hv
  apply funext
  intro i
  obtain ⟨j, hji⟩ := exists_ne i
  let f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := LinearMap.proj i
  have hf : f (Pi.single j 1) = 0 := by simp [f, hji.symm]
  let g := transvection (Pi.single j 1) f hf
  have he := congrFun (hv ⟨g, mem_top _⟩) j
  change v j + v i * ((Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) j) = v j at he
  simpa using he

/-- PSL simplicity transfers through the actual binary matrix equivalence. -/
theorem linear_simple (n : ℕ) (hn : 3 ≤ n) : IsSimpleGroup (LinearGroup n) := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
    Atlas.psl_simple_high_rank n hn
  exact (projectiveEquivLinear (by omega : 0 < n)).symm.isSimpleGroup

/-- The excluded two-dimensional actor is solvable through its S₃ action. -/
theorem linear_two_solvable : Group.IsSolvable (LinearGroup 2) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
  let e := (slEquivLinear 2).symm.trans (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep.ModelComponents

end
