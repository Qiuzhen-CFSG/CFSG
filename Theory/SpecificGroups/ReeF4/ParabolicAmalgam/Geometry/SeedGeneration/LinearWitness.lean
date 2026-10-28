module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.SplitRetraction.Grading
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.RootCurve

/-!
# A positive fixed element outside the linear Ree radical

The product of the two positive end-root elements at parameter one is fixed by
the Ree twist. Its root-zero, Cartan-one matrix entry is one, so it is
nonidentity over every Ree coefficient field. It lies in the end-node Levi;
the proved disjointness of that Levi from the linear radical therefore keeps
it outside the radical. This gives a nontrivial image of the positive subgroup
under any projection whose kernel is precisely that radical, including at q=2.

Source: the A₁ × A₁ Levi calculation underlying Aschbacher–Smith F.1.12(I)(5),
printed pp.263–264 of `refs/quasithin.pdf`. The ambient group is the full fixed
Ree group, and the witness uses only its explicit root matrices.
-/

public section

namespace ReeF4.Parabolics.SeedGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open OuterLocal.SuzukiCommutators LargeLocalSeeds Subgroup
noncomputable section

private theorem simple_matrix (m : ℕ) (i : Fin 4) (t : CoefficientField m) :
    (rootGeneratorInGroup m (typeF4SimpleRootIndex i) t).val.val =
      positiveMatrix (typeF4RootPairing_baseEquiv i) t := by
  change (F4Chevalley.rootCurve _ t).val = _
  simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple, positiveUnit_val]

private theorem end3_column (m : ℕ) (a : F4Chevalley.BasisIndex) :
    positiveMatrix (typeF4RootPairing_baseEquiv 3) (1 : CoefficientField m)
      a (Sum.inl (typeF4RootPairing_baseEquiv 1)) =
      (1 : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex (CoefficientField m))
        a (Sum.inl (typeF4RootPairing_baseEquiv 1)) := by
  cases a <;> simp [positiveMatrix_formula, eDividedPower, eMatrix,
    typeF4RootPairing_base_cartan_apply, typeF4CartanMatrix]

private theorem end0_entry (m : ℕ) :
    positiveMatrix (typeF4RootPairing_baseEquiv 0) (1 : CoefficientField m)
      (Sum.inr (typeF4SimpleRootIndex 0)) (Sum.inl (typeF4RootPairing_baseEquiv 1)) = 1 := by
  simp [positiveMatrix_formula, eDividedPower, eMatrix,
    typeF4RootPairing_baseEquiv_val, typeF4RootPairing_base_cartan_apply, typeF4CartanMatrix]

/-- The paired end-root element is nonidentity, including over the binary field. -/
theorem endRootWord_one_ne_one (m : ℕ) : endRootWord m 1 ≠ 1 := by
  intro h
  have he := congrArg (fun x : SplitGroup m =>
    x.val.val (Sum.inr (typeF4SimpleRootIndex 0))
      (Sum.inl (typeF4RootPairing_baseEquiv 1))) h
  simp only [endRootWord, map_one, Subgroup.coe_mul, Units.val_mul,
    simple_matrix, Matrix.mul_apply, end3_column, Matrix.one_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    end0_entry, Subgroup.coe_one, Units.val_one, reduceCtorEq, if_false] at he
  exact one_ne_zero he

/-- The positive fixed subgroup is not contained in the linear root radical. -/
theorem unipotent_not_le_linear_radical (m : ℕ) :
    ¬ unipotent m ≤ radical m .linear := by
  let x : Model m := ⟨endRootWord m 1, by
    apply (mem_fixedSubgroup m _).mpr
    have h := endRootWord_fixed (canonicalLocalBlockInput m) 1
    rwa [LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply] at h⟩
  have hx : x ∈ unipotent m := by
    change toSplitGroup m x ∈ splitUnipotent m
    rw [toSplitGroup_apply]
    exact splitRadical_le_unipotent m .suzuki (endRootWord_mem_radical m 1)
  have hl : endRootWord m 1 ∈ BinaryLinear.splitLevi m := by
    apply mul_mem
    · exact BinaryLinear.root_mem_splitLevi m _ _ ⟨0, by simp [leviNodes], Or.inl rfl⟩
    · exact BinaryLinear.root_mem_splitLevi m _ _ ⟨3, by simp [leviNodes], Or.inl rfl⟩
  intro h
  have hr : toSplitGroup m x ∈ splitRadical m .linear := h hx
  rw [toSplitGroup_apply] at hr
  exact endRootWord_one_ne_one m
    (Subgroup.disjoint_def.mp (BinaryLinear.splitRadical_disjoint_splitLevi m) hr hl)

end
end ReeF4.Parabolics.SeedGeneration
