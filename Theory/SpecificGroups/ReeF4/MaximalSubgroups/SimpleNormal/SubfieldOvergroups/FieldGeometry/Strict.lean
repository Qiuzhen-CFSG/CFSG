module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.Contracts
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.RootCurve

/-!
# Strict inclusions of the actual Ree subfield groups

A product of the two orthogonal end-root elements is twist-fixed. One of its
Cartan-column entries is exactly its free field parameter. Embedding this
word from the larger subfield, with a parameter not fixed by the smaller
Frobenius power, witnesses strictness. A polynomial root bound supplies such
a parameter. The argument includes the full binary Ree group and the ambient
upper endpoint, and uses neither field descent nor simplicity.

Source: the subfield case of Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E; arXiv:0910.4758, proof of Theorem 5,
case 10. The entry calculation extends the parameter-one calculation in
`ParabolicAmalgam/Geometry/SeedGeneration/LinearWitness.lean`.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open ReeF4 ReeF4.Subfield ReeF4.Parabolics
open ReeF4.Parabolics.OuterLocal.SuzukiCommutators

noncomputable section

namespace ReeF4.Subfield

private theorem simple_matrix (m : ℕ) (i : Fin 4) (t : CoefficientField m) :
    (rootGeneratorInGroup m (typeF4SimpleRootIndex i) t).val.val =
      positiveMatrix (typeF4RootPairing_baseEquiv i) t := by
  change (F4Chevalley.rootCurve _ t).val = _
  simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple, positiveUnit_val]

private theorem end3_column (m : ℕ) (t : CoefficientField m)
    (a : F4Chevalley.BasisIndex) :
    positiveMatrix (typeF4RootPairing_baseEquiv 3) t
      a (Sum.inl (typeF4RootPairing_baseEquiv 1)) =
      (1 : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex (CoefficientField m))
        a (Sum.inl (typeF4RootPairing_baseEquiv 1)) := by
  cases a <;> simp [positiveMatrix_formula, eDividedPower, eMatrix,
    typeF4RootPairing_base_cartan_apply, typeF4CartanMatrix]

private theorem end0_entry (m : ℕ) (t : CoefficientField m) :
    positiveMatrix (typeF4RootPairing_baseEquiv 0) t
      (Sum.inr (typeF4SimpleRootIndex 0)) (Sum.inl (typeF4RootPairing_baseEquiv 1)) = t := by
  simp [positiveMatrix_formula, eDividedPower, eMatrix,
    typeF4RootPairing_baseEquiv_val, typeF4RootPairing_base_cartan_apply, typeF4CartanMatrix]

/-- The end-root parameter is visible as an actual matrix entry. -/
theorem endRootWord_entry (m : ℕ) (t : CoefficientField m) :
    (endRootWord m t).val.val (Sum.inr (typeF4SimpleRootIndex 0))
      (Sum.inl (typeF4RootPairing_baseEquiv 1)) = t := by
  simp only [endRootWord, Subgroup.coe_mul, Units.val_mul,
    simple_matrix, Matrix.mul_apply, end3_column, Matrix.one_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, end0_entry]

/-- A proper smaller Frobenius power does not fix every coefficient. -/
theorem exists_pow_ne {k l : ℕ} (hkl : k < l) :
    ∃ t : CoefficientField l, t ^ (2 ^ (2 * k + 1)) ≠ t := by
  classical
  by_contra! h
  have hp : 1 < 2 ^ (2 * k + 1) := Nat.one_lt_pow (by omega) (by omega)
  have hc := Polynomial.card_le_degree_of_subset_roots
    (R := CoefficientField l) (p := Polynomial.X ^ (2 ^ (2 * k + 1)) - Polynomial.X)
    (Z := Finset.univ) (fun x _ => by
      rw [Polynomial.mem_roots']
      exact ⟨FiniteField.X_pow_card_sub_X_ne_zero _ hp, by
        simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, sub_eq_zero, h x]⟩)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, field_card,
    FiniteField.X_pow_card_sub_X_natDegree_eq _ hp] at hc
  exact (Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega : 2*k+1 < 2*l+1)).not_ge hc

end ReeF4.Subfield

namespace ReeF4.MaximalSubgroups.SimpleNormal

/-- Nested subfield fixed groups are strictly nested, including both endpoints. -/
theorem strictSubfieldInclusions : StrictSubfieldInclusions := by
  intro m k l hkl _hml hklD hlmD
  refine lt_of_le_not_ge (fixedSubfield_mono m hklD) ?_
  obtain ⟨f⟩ := nonempty_coefficientHom hlmD
  obtain ⟨t, ht⟩ := exists_pow_ne hkl
  let x : Model l := ⟨endRootWord l t, by
    apply (mem_fixedSubgroup l _).mpr
    simpa only [LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply]
      using endRootWord_fixed (canonicalLocalBlockInput l) t⟩
  intro hle
  have hx : reeMap hlmD f x ∈ fixedSubfield m k :=
    hle (reeMap_range_le hlmD f ⟨x, rfl⟩)
  have he := entry_pow_eq_of_mem_fixedSubfield hx
    (Sum.inr (typeF4SimpleRootIndex 0)) (Sum.inl (typeF4RootPairing_baseEquiv 1))
  rw [toSplitGroup_reeMap, toSplitGroup_apply] at he
  change f ((endRootWord l t).val.val _ _) ^ (2 ^ (2 * k + 1)) =
    f ((endRootWord l t).val.val _ _) at he
  rw [endRootWord_entry, ← map_pow] at he
  exact ht (f.injective he)

end ReeF4.MaximalSubgroups.SimpleNormal
