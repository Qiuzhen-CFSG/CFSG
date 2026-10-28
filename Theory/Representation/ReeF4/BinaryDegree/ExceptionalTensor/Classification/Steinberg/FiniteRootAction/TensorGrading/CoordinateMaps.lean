module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading.TensorSpaces

/-!
# Linear insertion of one factor operator

A tensor endomorphism acting in one specified factor and identically in the
others is linear in that factor operator. Its root coefficients therefore
inherit the exact single-factor deficit shift inside the canonical tensor.
These insertions are the leading operators for finite ordinary Frobenius.

Source: Steinberg (1963), Section 12.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
open Theory.AlgebraicGroup
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

theorem tensorMap_congr (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (S T : ∀ i : ℕ, Module.End F (basicFactor m B i).Space) (n : ℕ)
    (h : ∀ i < n, S i = T i) : tensorMap m B S n = tensorMap m B T n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change TensorProduct.map (tensorMap m B S n) (S n) =
      TensorProduct.map (tensorMap m B T n) (T n)
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

/-- Insert a single endomorphism; the prefix length is explicit. -/
@[expose] def coordinateMap (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (n i : ℕ) (A : Module.End F (basicFactor m B i).Space) :
    Module.End F (basicTensorSpace m B n) := tensorMap m B (Pi.mulSingle i A) n

theorem coordinateMap_one (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (n i : ℕ) : coordinateMap m B n i 1 = 1 := by
  simp only [coordinateMap, Pi.mulSingle_one]
  exact tensorMap_one m B n

private theorem coordinateMap_outside (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (n i : ℕ) (h : n ≤ i)
    (A : Module.End F (basicFactor m B i).Space) : coordinateMap m B n i A = 1 := by
  rw [← tensorMap_one m B n]
  apply tensorMap_congr
  intro j hj
  exact Pi.mulSingle_eq_of_ne (M := fun j => Module.End F (basicFactor m B j).Space)
    (by omega : j ≠ i) A

/-- The new last factor acts identically on the preceding prefix. -/
theorem coordinateMap_last (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (n : ℕ) (A : Module.End F (basicFactor m B n).Space) :
    coordinateMap m B (n + 1) n A = TensorProduct.map (1 : Module.End F (basicTensorSpace m B n)) A := by
  change TensorProduct.map (coordinateMap m B n n A)
    ((Pi.mulSingle n A : ∀ j, Module.End F (basicFactor m B j).Space) n) = _
  rw [coordinateMap_outside m B n n le_rfl, Pi.mulSingle_eq_same]

/-- An earlier coordinate extends by the identity in the last factor. -/
theorem coordinateMap_cast (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (n i : ℕ) (hi : i < n) (A : Module.End F (basicFactor m B i).Space) :
    coordinateMap m B (n + 1) i A =
      TensorProduct.map (coordinateMap m B n i A) (1 : Module.End F (basicFactor m B n).Space) := by
  change TensorProduct.map (coordinateMap m B n i A)
    ((Pi.mulSingle i A : ∀ j, Module.End F (basicFactor m B j).Space) n) = _
  rw [Pi.mulSingle_eq_of_ne (M := fun j => Module.End F (basicFactor m B j).Space)
    (Nat.ne_of_gt hi) A]

private theorem coordinateMap_add (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (n i : ℕ) (hi : i < n)
    (A D : Module.End F (basicFactor m B i).Space) :
    coordinateMap m B n i (A + D) = coordinateMap m B n i A + coordinateMap m B n i D := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with rfl | h
    · rw [coordinateMap_last, coordinateMap_last, coordinateMap_last]
      exact TensorProduct.map_add_right _ _ _
    · rw [coordinateMap_cast m B n i h, coordinateMap_cast m B n i h,
        coordinateMap_cast m B n i h, ih h]
      exact TensorProduct.map_add_left _ _ _

private theorem coordinateMap_smul (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (n i : ℕ) (hi : i < n)
    (c : F) (A : Module.End F (basicFactor m B i).Space) :
    coordinateMap m B n i (c • A) = c • coordinateMap m B n i A := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with rfl | h
    · rw [coordinateMap_last, coordinateMap_last]
      exact TensorProduct.map_smul_right _ _ _
    · rw [coordinateMap_cast m B n i h, coordinateMap_cast m B n i h, ih h]
      exact TensorProduct.map_smul_left _ _ _

/-- Linear insertion of a genuine coordinate of the prefix. -/
def coordinateLinearMap (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (n i : ℕ) (hi : i < n) :
    Module.End F (basicFactor m B i).Space →ₗ[F] Module.End F (basicTensorSpace m B n) where
  toFun := coordinateMap m B n i
  map_add' := coordinateMap_add m B n i hi
  map_smul' := coordinateMap_smul m B n i hi

theorem coordinateLinearMap_apply (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (n i : ℕ) (hi : i < n)
    (A : Module.End F (basicFactor m B i).Space) :
    coordinateLinearMap m B n i hi A = coordinateMap m B n i A := by rfl

/-- A single root coefficient shifts the tensor filtration by its full degree. -/
theorem coordinateCoefficient_filtration (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (n i : ℕ) (hi : i < n)
    (p : AlgebraicTensor.RootExpansion (basicFactor m B i).action)
    (r : F4Chevalley.Root) (a : ℕ) (η : ℕ → EndNode.Weight) (k : ℤ) :
    (tensorFiltration m B η n k).map (coordinateMap m B n i (p.coeff r a)) ≤
      tensorFiltration m B η n (k - (a : ℤ) * weightDegree (rootWeight r)) := by
  have h := tensorMap_filtration m B (Pi.mulSingle i (p.coeff r a)) η
    (Pi.single i (a • rootWeight r)) n (by
      intro j _ μ v hv
      by_cases hji : j = i
      · subst j
        simpa only [Pi.mulSingle_eq_same, Pi.single_eq_same] using
          coeff_mem_corootWeightSpace (basicFactor m B i) p r a μ hv
      · simpa only [Pi.mulSingle_eq_of_ne hji, Pi.single_eq_of_ne hji,
          Module.End.one_apply, add_zero] using hv) k
  have hs : (∑ j ∈ Finset.range n, weightDegree ((Pi.single i (a • rootWeight r) : ℕ → EndNode.Weight) j)) =
      (a : ℤ) * weightDegree (rootWeight r) := by
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, weightDegree_nsmul]
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji]
      simp [weightDegree]
    · exact fun hni => (hni (Finset.mem_range.mpr hi)).elim
  simpa only [coordinateMap, hs] using h

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
