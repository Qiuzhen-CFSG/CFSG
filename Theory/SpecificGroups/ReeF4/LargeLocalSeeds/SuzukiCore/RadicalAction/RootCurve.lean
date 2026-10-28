module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.RootCurve

/-!
# A faithful parameter on the fixed end-root curve

The entry in root row 0 and Cartan column 1 of the paired end-root word is
its parameter. The root-3 factor fixes this Cartan column, and the root-0
factor contributes the parameter through the adjacent Cartan entry.
Consequently the curve inside the fixed Suzuki seed is injective.

This extends the parameter-one calculation in
`ParabolicAmalgam/Geometry/SeedGeneration/LinearWitness.lean`. It detects the
nontrivial scalar action used to prove self-centralization of the Suzuki
radical, without a radical order calculation or a fixed-coordinate catalogue.

Source: the twisted F₄ root construction underlying Aschbacher–Smith,
F.1.12(I)(5), printed p.263, and its local characteristic-two application
in 2.3.9(7), printed p.526 of `refs/quasithin.pdf`.
-/

public section

namespace ReeF4.LargeLocalSeeds.SuzukiRadicalAction
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open Parabolics.OuterLocal.SuzukiCommutators
noncomputable section

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

/-- A Cartan-to-root entry recovers the first end-root parameter. -/
theorem endRootWord_entry (m : ℕ) (t : CoefficientField m) :
    (endRootWord m t).val.val (Sum.inr (typeF4SimpleRootIndex 0))
      (Sum.inl (typeF4RootPairing_baseEquiv 1)) = t := by
  simp only [endRootWord, Subgroup.coe_mul, Units.val_mul,
    simple_matrix, Matrix.mul_apply, end3_column, Matrix.one_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, end0_entry]

/-- The actual fixed radical curve distinguishes its field parameters. -/
theorem endRootElement_injective {m : ℕ} (d : LocalBlockInput m) :
    Function.Injective (endRootElement d) := by
  intro t u h
  have he := congrArg (fun x : standardSeed d .suzuki =>
    x.val.val.val.val (Sum.inr (typeF4SimpleRootIndex 0))
      (Sum.inl (typeF4RootPairing_baseEquiv 1))) h
  exact (endRootWord_entry m t).symm.trans (he.trans (endRootWord_entry m u))
end
end ReeF4.LargeLocalSeeds.SuzukiRadicalAction
