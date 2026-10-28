module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.BasicTensorDefs
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading.CoefficientWeights

/-!
# Unweighted tensor weight spaces and their integral filtration

The prefix weight space is the tensor product of the actual weight spaces
of its individual factors. Its degree is the sum of the individual highest
weight deficits, with no Frobenius multipliers. Factorwise linear maps with
specified weight shifts therefore have the sum of those shifts on this
filtration. This separates scalar polynomial exponents from weight deficits.

Source: Steinberg (1963), Section 12, tensor-product leading-term argument.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction

open Theory.AlgebraicGroup
open scoped TensorProduct
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

/-- The tensor product of a family of factor endomorphisms on the canonical space. -/
@[expose] def tensorMap (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (T : ∀ i : ℕ, Module.End F (basicFactor m B i).Space) :
    (n : ℕ) → Module.End F (basicTensorSpace m B n)
  | 0 => 1
  | n + 1 => TensorProduct.map (tensorMap m B T n) (T n)

theorem tensorMap_one (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F) (n : ℕ) :
    tensorMap m B (fun _ => 1) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change TensorProduct.map (tensorMap m B (fun _ => 1) n)
      (1 : Module.End F (basicFactor m B n).Space) = 1
    rw [ih]
    exact TensorProduct.map_one

theorem tensorMap_mul (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (S T : ∀ i : ℕ, Module.End F (basicFactor m B i).Space) (n : ℕ) :
    tensorMap m B (fun i => S i * T i) n = tensorMap m B S n * tensorMap m B T n := by
  induction n with
  | zero => exact (one_mul _).symm
  | succ n ih =>
    change TensorProduct.map (tensorMap m B (fun i => S i * T i) n) (S n * T n) =
      TensorProduct.map (tensorMap m B S n) (S n) * TensorProduct.map (tensorMap m B T n) (T n)
    rw [ih]
    exact TensorProduct.map_mul _ _ _ _

/-- Tensor the actual coroot weight spaces of the first `n` factors. -/
@[expose] def tensorWeightSpace (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (μ : ℕ → EndNode.Weight) : (n : ℕ) → Submodule F (basicTensorSpace m B n)
  | 0 => ⊤
  | n + 1 => Submodule.map₂ (TensorProduct.mk F _ _)
      (tensorWeightSpace m B μ n) (EndNode.corootWeightSpace (basicFactor m B n) (μ n))

/-- The sum of the individual factor deficits, without Frobenius weights. -/
@[expose] def tensorDeficit (η μ : ℕ → EndNode.Weight) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, weightDegree (η i - μ i)

/-- Increasing filtration by the unweighted tensor deficit. -/
@[expose] def tensorFiltration (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (η : ℕ → EndNode.Weight) (n : ℕ) (k : ℤ) : Submodule F (basicTensorSpace m B n) :=
  ⨆ μ : ℕ → EndNode.Weight, ⨆ (_ : tensorDeficit η μ n ≤ k), tensorWeightSpace m B μ n

theorem tensorWeightSpace_le_filtration (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (η μ : ℕ → EndNode.Weight)
    (n : ℕ) {k : ℤ} (h : tensorDeficit η μ n ≤ k) :
    tensorWeightSpace m B μ n ≤ tensorFiltration m B η n k :=
  le_iSup_of_le μ (le_iSup_of_le h le_rfl)

theorem tensorFiltration_mono (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (η : ℕ → EndNode.Weight) (n : ℕ) : Monotone (tensorFiltration m B η n) := by
  intro k l h
  apply iSup_le
  intro μ
  apply iSup_le
  intro hμ
  exact tensorWeightSpace_le_filtration m B η μ n (hμ.trans h)

/-- Factorwise exact weight shifts tensor to exact multidegree shifts. -/
theorem tensorMap_weightSpace (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (T : ∀ i : ℕ, Module.End F (basicFactor m B i).Space)
    (μ ν : ℕ → EndNode.Weight) (n : ℕ)
    (hT : ∀ i < n, ∀ v ∈ EndNode.corootWeightSpace (basicFactor m B i) (μ i),
      T i v ∈ EndNode.corootWeightSpace (basicFactor m B i) (ν i)) :
    (tensorWeightSpace m B μ n).map (tensorMap m B T n) ≤ tensorWeightSpace m B ν n := by
  induction n with
  | zero => exact le_top
  | succ n ih =>
    change (Submodule.map₂ (TensorProduct.mk F _ _) (tensorWeightSpace m B μ n)
      (EndNode.corootWeightSpace (basicFactor m B n) (μ n))).map
      (TensorProduct.map (tensorMap m B T n) (T n)) ≤
      Submodule.map₂ (TensorProduct.mk F _ _) (tensorWeightSpace m B ν n)
        (EndNode.corootWeightSpace (basicFactor m B n) (ν n))
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.map₂_le.mpr
    intro x hx y hy
    change (tensorMap m B T n x) ⊗ₜ[F] (T n y) ∈
      Submodule.map₂ (TensorProduct.mk F _ _) (tensorWeightSpace m B ν n)
        (EndNode.corootWeightSpace (basicFactor m B n) (ν n))
    exact Submodule.apply_mem_map₂ _
      (ih (fun i hi => hT i (Nat.lt_succ_of_lt hi)) (Submodule.mem_map_of_mem hx))
      (hT n (Nat.lt_succ_self n) y hy)

/-- Every coefficient in every factor has the expected tensor weight shift. -/
theorem tensorCoefficient_weightSpace (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (p : ∀ i : ℕ, AlgebraicTensor.RootExpansion (basicFactor m B i).action)
    (r : ℕ → F4Chevalley.Root) (a : ℕ → ℕ) (μ : ℕ → EndNode.Weight) (n : ℕ) :
    (tensorWeightSpace m B μ n).map (tensorMap m B (fun i => (p i).coeff (r i) (a i)) n) ≤
      tensorWeightSpace m B (fun i => μ i + a i • rootWeight (r i)) n := by
  apply tensorMap_weightSpace
  intro i _ v hv
  exact coeff_mem_corootWeightSpace (basicFactor m B i) (p i) (r i) (a i) (μ i) hv

/-- Adding factor weights subtracts exactly their total unweighted degree. -/
theorem tensorDeficit_add (η μ δ : ℕ → EndNode.Weight) (n : ℕ) :
    tensorDeficit η (fun i => μ i + δ i) n =
      tensorDeficit η μ n - ∑ i ∈ Finset.range n, weightDegree (δ i) := by
  simp only [tensorDeficit, weightDegree_sub, weightDegree_add, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Uniform shifts of the individual weight spaces give a filtration shift. -/
theorem tensorMap_filtration (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (T : ∀ i : ℕ, Module.End F (basicFactor m B i).Space)
    (η δ : ℕ → EndNode.Weight) (n : ℕ)
    (hT : ∀ i < n, ∀ μ v, v ∈ EndNode.corootWeightSpace (basicFactor m B i) μ →
      T i v ∈ EndNode.corootWeightSpace (basicFactor m B i) (μ + δ i)) (k : ℤ) :
    (tensorFiltration m B η n k).map (tensorMap m B T n) ≤
      tensorFiltration m B η n (k - ∑ i ∈ Finset.range n, weightDegree (δ i)) := by
  rw [Submodule.map_le_iff_le_comap]
  apply iSup_le
  intro μ
  apply iSup_le
  intro hμ
  rw [← Submodule.map_le_iff_le_comap]
  refine (tensorMap_weightSpace m B T μ (fun i => μ i + δ i) n
    (fun i hi v hv => hT i hi (μ i) v hv)).trans ?_
  apply tensorWeightSpace_le_filtration
  rw [tensorDeficit_add]
  exact sub_le_sub_right hμ _

/-- Actual rational coefficients have their unweighted filtration shift. -/
theorem tensorCoefficient_filtration (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (p : ∀ i : ℕ, AlgebraicTensor.RootExpansion (basicFactor m B i).action)
    (r : ℕ → F4Chevalley.Root) (a : ℕ → ℕ) (η : ℕ → EndNode.Weight) (n : ℕ) (k : ℤ) :
    (tensorFiltration m B η n k).map (tensorMap m B (fun i => (p i).coeff (r i) (a i)) n) ≤
      tensorFiltration m B η n
        (k - ∑ i ∈ Finset.range n, (a i : ℤ) * weightDegree (rootWeight (r i))) := by
  simpa only [weightDegree_nsmul] using tensorMap_filtration m B
    (fun i => (p i).coeff (r i) (a i)) η (fun i => a i • rootWeight (r i)) n
    (fun i _ μ v hv => coeff_mem_corootWeightSpace (basicFactor m B i) (p i)
      (r i) (a i) μ hv) k

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
