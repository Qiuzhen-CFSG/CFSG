module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading.OrdinaryPoints

/-!
# Positive ordinary Frobenius root action to first filtered order

Each actual root polynomial is linear to first filtered order: its coefficient
of exponent `a` loses `a` root degrees. The tensor root action is the product of
its coordinate insertions. Cross terms lose at least two root degrees, while
the surviving terms have scalars `t^(2^i)` and the genuine coefficient-one
operator in factor `i`.

Source: Steinberg (1963), Section 12, finite Frobenius separation argument.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
open Theory.AlgebraicGroup StandardRootSystem
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

omit [IsAlgClosed F] in
private theorem list_hasLeadingTerm {V : Type*} [AddCommGroup V] [Module F V]
    (C : ℤ → Submodule F V) (hC : Monotone C) (d : ℤ) (hd : 0 < d)
    {I : Type*} (w : List I) (A L : I → Module.End F V)
    (h : ∀ i ∈ w, HasLeadingTerm C d (A i) (L i)) :
    HasLeadingTerm C d (w.map A).prod (w.map L).sum := by
  induction w with
  | nil =>
    constructor
    · exact (loweringOperators C d).zero_mem
    · simp only [List.map_nil, List.prod_nil, List.sum_nil, sub_self]
      exact (loweringOperators C (d + 1)).zero_mem
  | cons a w ih =>
    exact (h a List.mem_cons_self).mul hC hd
      (ih fun i hi => h i (List.mem_cons_of_mem a hi))

/-- The polynomial of one genuine coordinate has its coefficient one as leading term. -/
theorem coordinateRoot_hasLeadingTerm (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (n i : ℕ) (hi : i < n)
    (p : AlgebraicTensor.RootExpansion (basicFactor m B i).action)
    (η : ℕ → EndNode.Weight) (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (t : F) :
    HasLeadingTerm (tensorFiltration m B η n) (weightDegree (rootWeight r))
      (coordinateMap m B n i ((basicFactor m B i).action.action (algebraicRootElement r t)))
      (t • coordinateMap m B n i (p.coeff r 1)) := by
  let L := coordinateLinearMap m B n i hi
  let q := (p.coeff r).mapRange L (map_zero L)
  have hqa (a : ℕ) : q a = coordinateMap m B n i (p.coeff r a) := by
    simp only [q, Finsupp.mapRange_apply, L, coordinateLinearMap_apply]
  have hq0 : q 0 = 1 := by
    rw [hqa, p.coeff_zero]
    exact coordinateMap_one m B n i
  have hq (a : ℕ) : q a ∈ loweringOperators (tensorFiltration m B η n)
      ((a : ℤ) * weightDegree (rootWeight r)) := by
    rw [hqa]
    intro k v hv
    exact coordinateCoefficient_filtration m B n i hi p r a η k
      (Submodule.mem_map_of_mem hv)
  have heval : q.sum (fun a A => t ^ a • A) =
      coordinateMap m B n i ((basicFactor m B i).action.action (algebraicRootElement r t)) := by
    rw [Finsupp.sum_mapRange_index (by simp)]
    change (p.coeff r).sum (fun a A => t ^ a • L A) = _
    simp only [Finsupp.sum, ← map_smul, ← map_sum]
    change L ((p.coeff r).sum (fun a A => t ^ a • A)) = _
    rw [p.eval_eq]
    exact coordinateLinearMap_apply m B n i hi _
  have h := polynomial_hasLeadingTerm (tensorFiltration m B η n)
    (tensorFiltration_mono m B η n) (weightDegree (rootWeight r))
    (weightDegree_rootWeight_pos hr) q hq0 hq t
  rw [heval, hqa] at h
  exact h

variable [CharP F 2]

/-- The first filtered term of the actual ordinary Frobenius root action. -/
theorem ordinaryPointAction_root_hasLeadingTerm (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (n : ℕ)
    (p : ∀ i : ℕ, AlgebraicTensor.RootExpansion (basicFactor m B i).action)
    (η : ℕ → EndNode.Weight) (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (t : F) :
    HasLeadingTerm (tensorFiltration m B η n) (weightDegree (rootWeight r))
      (ordinaryPointAction m B n (algebraicRootElement r t))
      (((List.range n).map fun i => t ^ (2 ^ i) •
        coordinateMap m B n i ((p i).coeff r 1)).sum) := by
  rw [ordinaryPointAction_root]
  exact list_hasLeadingTerm _ (tensorFiltration_mono m B η n) _
    (weightDegree_rootWeight_pos hr) (List.range n) _ _ fun i hi =>
      coordinateRoot_hasLeadingTerm m B n i (List.mem_range.mp hi) (p i) η r hr _

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
