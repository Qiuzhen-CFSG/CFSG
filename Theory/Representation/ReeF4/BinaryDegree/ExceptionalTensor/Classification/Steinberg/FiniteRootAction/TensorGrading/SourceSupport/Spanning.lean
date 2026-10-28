module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading.SourceSupport.DegreeSpaces

/-!
# Spanning and the marked degree-zero tensor

The actual coroot weight spaces of every basic source factor span. Tensoring
this decomposition gives all canonical tensor weight spaces. The tensor of
the actual highest vectors belongs to its marked degree-zero homogeneous
space. These are the two source inputs to the finite degree-support argument.

Source: Steinberg (1963), Sections 5 and 12.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
open Theory.AlgebraicGroup
open scoped TensorProduct
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

private theorem tensorWeightSpace_congr (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F) (μ ν : ℕ → EndNode.Weight) (n : ℕ)
    (h : ∀i<n, μ i = ν i) : tensorWeightSpace m B μ n = tensorWeightSpace m B ν n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Submodule.map₂ (TensorProduct.mk F _ _) (tensorWeightSpace m B μ n)
      (EndNode.corootWeightSpace (basicFactor m B n) (μ n)) =
      Submodule.map₂ (TensorProduct.mk F _ _) (tensorWeightSpace m B ν n)
        (EndNode.corootWeightSpace (basicFactor m B n) (ν n))
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

/-- Tensoring the actual spanning decompositions spans the canonical prefix. -/
theorem tensorWeightSpace_iSup_eq_top (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F)
    (hw : ∀i, (⨆ μ : EndNode.Weight, EndNode.corootWeightSpace (basicFactor m B i) μ) = ⊤)
    (n : ℕ) : (⨆ μ : ℕ → EndNode.Weight, tensorWeightSpace m B μ n) = ⊤ := by
  classical
  induction n with
  | zero => simp [tensorWeightSpace]
  | succ n ih =>
    apply top_unique
    change (⊤ : Submodule F (basicTensorSpace m B n ⊗[F] (basicFactor m B n).Space)) ≤ _
    rw [← TensorProduct.map₂_mk_top_top_eq_top F (basicTensorSpace m B n) (basicFactor m B n).Space,
      ← ih, ← hw n, Submodule.map₂_iSup_left]
    apply iSup_le
    intro μ
    rw [Submodule.map₂_iSup_right]
    apply iSup_le
    intro ν
    have he : tensorWeightSpace m B μ n = tensorWeightSpace m B (Function.update μ n ν) n := by
      apply tensorWeightSpace_congr
      intro i hi
      rw [Function.update_of_ne (Nat.ne_of_lt hi)]
    apply le_iSup_of_le (Function.update μ n ν)
    change _ ≤ Submodule.map₂ (TensorProduct.mk F _ _)
      (tensorWeightSpace m B (Function.update μ n ν) n)
      (EndNode.corootWeightSpace (basicFactor m B n) (Function.update μ n ν n))
    rw [Function.update_self, ← he]

/-- The genuine highest-vector tensor has homogeneous degree zero. -/
theorem highestTensor_mem_degree_zero (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F) (η : ℕ → EndNode.Weight)
    (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, v i ∈ EndNode.corootWeightSpace (basicFactor m B i) (η i)) (n : ℕ) :
    highestTensor m B v n ∈ tensorDegreeSpace m B η n 0 := by
  have hm : highestTensor m B v n ∈ tensorWeightSpace m B η n := by
    induction n with
    | zero => trivial
    | succ n ih => exact Submodule.apply_mem_map₂ _ ih (hv n)
  apply Submodule.mem_iSup_of_mem η
  apply Submodule.mem_iSup_of_mem (show tensorDeficit η η n = 0 by
    simp [tensorDeficit, weightDegree])
  exact hm

/-- Every integer homogeneous space together spans the actual prefix. -/
theorem tensorDegreeSpace_iSup_eq_top (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F) (η : ℕ → EndNode.Weight)
    (hw : ∀i, (⨆ μ : EndNode.Weight, EndNode.corootWeightSpace (basicFactor m B i) μ) = ⊤)
    (n : ℕ) : (⨆ k, tensorDegreeSpace m B η n k) = ⊤ := by
  apply top_unique
  rw [← tensorWeightSpace_iSup_eq_top m B hw n]
  apply iSup_le
  intro μ
  exact le_iSup_of_le (tensorDeficit η μ n) (le_iSup_of_le μ (le_iSup_of_le rfl le_rfl))

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
