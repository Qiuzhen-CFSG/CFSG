module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading.CoordinateMaps
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.PrefixPrimitives

/-!
# Actual integer homogeneous spaces of the basic tensor

Group the tensor weight spaces by their unweighted highest-weight deficit.
The literal coroot one-torus with exponents `(16,30,21,11)` acts on each
such space by its corresponding integer character. Distinct characters over
the algebraically closed field separate the homogeneous spaces. The actual
coordinate root coefficients shift their degrees by the native root degree.

Source: Steinberg (1963), Section 12, weight filtration.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
open Theory.AlgebraicGroup StandardRootSystem
open scoped TensorProduct
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

/-- The actual integer homogeneous tensor space. -/
@[expose] def tensorDegreeSpace (m : ℕ) (B : ZMod (2*m+1) → AlgebraicFactor F)
    (η : ℕ → EndNode.Weight) (n : ℕ) (k : ℤ) : Submodule F (basicTensorSpace m B n) :=
  ⨆ μ : ℕ → EndNode.Weight, ⨆ (_ : tensorDeficit η μ n = k), tensorWeightSpace m B μ n

theorem tensorFiltration_eq_degree_iSup (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F) (η : ℕ → EndNode.Weight) (n : ℕ) (k : ℤ) :
    tensorFiltration m B η n k = ⨆ d ≤ k, tensorDegreeSpace m B η n d := by
  apply le_antisymm
  · apply iSup_le
    intro μ
    apply iSup_le
    intro hμ
    exact le_iSup_of_le (tensorDeficit η μ n) (le_iSup_of_le hμ
      (le_iSup_of_le μ (le_iSup_of_le rfl le_rfl)))
  · apply iSup_le
    intro d
    apply iSup_le
    intro hd
    apply iSup_le
    intro μ
    apply iSup_le
    intro hμ
    exact tensorWeightSpace_le_filtration m B η μ n (hμ.trans_le hd)

private def degreeTorus (B : AlgebraicFactor F) (t : Fˣ) : Module.End F B.Space :=
  (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex 0) (t ^ 16))).val *
  (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex 1) (t ^ 30))).val *
  (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex 2) (t ^ 21))).val *
  (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex 3) (t ^ 11))).val

private theorem degreeTorus_weight (B : AlgebraicFactor F) (t : Fˣ)
    (μ : EndNode.Weight) {v : B.Space} (hv : v ∈ EndNode.corootWeightSpace B μ) :
    degreeTorus B t v = (t : F) ^ weightDegree μ • v := by
  have h := (EndNode.mem_corootWeightSpace B μ v).mp hv
  simp only [degreeTorus, Module.End.mul_apply, h, map_smul, smul_smul,
    Units.val_pow_eq_pow_val]
  congr 1
  simp only [weightDegree, zpow_add₀ t.ne_zero, zpow_mul]
  norm_num only [zpow_ofNat]
  ac_rfl

private theorem tensorWeightSpace_eigen (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F) (μ : ℕ → EndNode.Weight)
    (n : ℕ) (t : Fˣ) : tensorWeightSpace m B μ n ≤
      Module.End.eigenspace (tensorMap m B (fun i => degreeTorus (basicFactor m B i) t) n)
        ((t : F) ^ (∑ i ∈ Finset.range n, weightDegree (μ i))) := by
  induction n with
  | zero =>
    intro x _
    exact Module.End.mem_eigenspace_iff.mpr (by simp [tensorMap])
  | succ n ih =>
    change Submodule.map₂ (TensorProduct.mk F _ _) (tensorWeightSpace m B μ n)
      (EndNode.corootWeightSpace (basicFactor m B n) (μ n)) ≤
      Module.End.eigenspace (TensorProduct.map
        (tensorMap m B (fun i => degreeTorus (basicFactor m B i) t) n)
        (degreeTorus (basicFactor m B n) t)) _
    apply Submodule.map₂_le.mpr
    intro x hx y hy
    apply Module.End.mem_eigenspace_iff.mpr
    change (tensorMap m B (fun i => degreeTorus (basicFactor m B i) t) n x) ⊗ₜ[F]
      degreeTorus (basicFactor m B n) t y = _
    rw [Module.End.mem_eigenspace_iff.mp (ih hx), degreeTorus_weight _ _ _ hy]
    rw [Finset.sum_range_succ, zpow_add₀ t.ne_zero]
    exact TensorProduct.smul_tmul_smul _ _ _ _

private theorem degreeCharacter_injective :
    Function.Injective (fun z : ℤ => fun t : Fˣ => (t : F) ^ z) := by
  intro a b h
  by_contra hab
  obtain ⟨t, ht⟩ := exists_unit_zpow_ne_one (k := F) (sub_ne_zero.mpr hab)
  apply ht
  rw [zpow_sub, mul_inv_eq_one]
  apply Units.ext
  simpa only [Units.val_zpow_eq_zpow_val] using congrFun h t

/-- Actual coroot characters make the integer homogeneous tensor spaces independent. -/
theorem tensorDegreeSpace_iSupIndep (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F) (η : ℕ → EndNode.Weight) (n : ℕ) :
    iSupIndep (tensorDegreeSpace m B η n) := by
  let H := ∑ i ∈ Finset.range n, weightDegree (η i)
  have hi := (Bor1.iSupIndep_commonEigenspaces
    (fun t : Fˣ => tensorMap m B (fun i => degreeTorus (basicFactor m B i) t) n)).comp
    (show Function.Injective (fun k : ℤ => fun t : Fˣ => (t : F) ^ (H-k)) from by
      intro a b h
      have := degreeCharacter_injective h
      omega)
  apply hi.mono
  intro k
  apply iSup_le
  intro μ
  apply iSup_le
  intro hμ
  apply le_iInf
  intro t
  have he : ∑ i ∈ Finset.range n, weightDegree (μ i) = H-k := by
    have hh : tensorDeficit η μ n = H - ∑ i ∈ Finset.range n, weightDegree (μ i) := by
      simp only [tensorDeficit, weightDegree_sub, Finset.sum_sub_distrib, H]
    rw [hh] at hμ
    omega
  simp only
  rw [← he]
  exact tensorWeightSpace_eigen m B μ n t

/-- Single-coordinate first root coefficients shift the exact integer degree. -/
theorem coordinateCoefficient_degreeSpace (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F) (η : ℕ → EndNode.Weight)
    (n i : ℕ) (hi : i < n) (p : AlgebraicTensor.RootExpansion (basicFactor m B i).action)
    (r : F4Chevalley.Root) (k : ℤ) :
    (tensorDegreeSpace m B η n k).map (coordinateMap m B n i (p.coeff r 1)) ≤
      tensorDegreeSpace m B η n (k-weightDegree (rootWeight r)) := by
  classical
  rw [Submodule.map_le_iff_le_comap]
  apply iSup_le
  intro μ
  apply iSup_le
  intro hμ
  rw [← Submodule.map_le_iff_le_comap]
  let δ : ℕ → EndNode.Weight := Pi.single i (rootWeight r)
  have hshift := tensorMap_weightSpace m B (Pi.mulSingle i (p.coeff r 1)) μ
    (fun j => μ j + δ j) n (by
      intro j _ v hv
      by_cases hji : j = i
      · subst j
        simpa only [Pi.mulSingle_eq_same, δ, Pi.single_eq_same, one_smul] using
          coeff_mem_corootWeightSpace (basicFactor m B i) p r 1 (μ i) hv
      · simpa only [Pi.mulSingle_eq_of_ne hji, δ, Pi.single_eq_of_ne hji,
          Module.End.one_apply, add_zero] using hv)
  apply hshift.trans
  apply le_iSup_of_le (fun j => μ j + δ j)
  refine le_iSup_of_le ?_ le_rfl
  · rw [tensorDeficit_add, hμ]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp only [δ, Pi.single_eq_same]
    · intro j _ hji
      simp only [δ, Pi.single_eq_of_ne hji, weightDegree, Pi.zero_apply, mul_zero, add_zero]
    · exact fun h => (h (Finset.mem_range.mpr hi)).elim

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
