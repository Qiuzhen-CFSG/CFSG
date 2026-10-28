module
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.LocalActions.RootGeometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.RootPartition
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup.Commutation

/-!
# The elementary abelian linear Ree block

A positive root supported on the two end nodes is one of those two simple
roots. Their integral Cartan pairing is zero, so their root curves commute.
The entire generated split subgroup is therefore commutative; in characteristic
two every element also has square one. Both properties pass to the actual
fixed intersection `simpleBlock m .linear true` by the faithful matrix map.

This verifies the abelian side of the distinction between types VI and V
in GLS3 Table 2.4, used in the root-permutation step of Steinberg's Theorem 36
(`refs/KGroup/GLS3/chapter2.tex` and `Chapter2St1.tex`). Noncommutativity of
the Suzuki block and recognition of the root family are separate obligations.
No assertion identifying a full block with a chosen parameter curve is used.
-/

noncomputable section
namespace ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.LocalActions
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open RootPairing.IntegralGeckConstruction LargeLocalSeeds
open LocalBlockInput.PairRigidity
open RadicalCoordinates.FixedCoordinates.RootPartition

private theorem positive_linear_root {r : F4Chevalley.Root}
    (hr : IsSimpleBlockRoot .linear true r) :
    r = typeF4SimpleRootIndex 0 ∨ r = typeF4SimpleRootIndex 3 := by
  have h1 := hr.1 1 (by simp [leviNodes, Fin.ext_iff])
  have h2 := hr.1 2 (by simp [leviNodes, Fin.ext_iff])
  obtain ⟨i, hi⟩ := table_exhaustive r hr.2
  rw [← hi, table_simpleCoefficient] at h1 h2
  have hi' : i = 0 ∨ i = 1 := by
    fin_cases i <;> norm_num [coefficients, Matrix.cons_val_two, Matrix.cons_val_three] at *
  rcases hi' with rfl | rfl
  · exact Or.inl (Subtype.ext hi.symm)
  · apply Or.inr
    apply Subtype.ext
    rw [← hi]
    ext j
    fin_cases j <;> norm_num [table, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem end_roots_commute (m : ℕ) (t u : CoefficientField m) :
    Commute (rootGeneratorInGroup m (typeF4SimpleRootIndex 0) t)
      (rootGeneratorInGroup m (typeF4SimpleRootIndex 3) u) := by
  have h := RootPairing.SimpleGeckGroup.commute_positive_positive_of_cartan_eq_zero
    (typeF4RootPairing_baseEquiv 0) (typeF4RootPairing_baseEquiv 3)
    (by intro h; have := typeF4RootPairing_baseEquiv.injective h; contradiction)
    (by rw [typeF4RootPairing_base_cartan_apply]; norm_num [typeF4CartanMatrix, Fin.ext_iff]) t u
  apply Subtype.ext
  change F4Chevalley.rootCurve _ t * F4Chevalley.rootCurve _ u =
    F4Chevalley.rootCurve _ u * F4Chevalley.rootCurve _ t
  simpa only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple] using
    show RootPairing.SimpleGeckGroup.positiveUnit (typeF4RootPairing_baseEquiv 0) t *
        RootPairing.SimpleGeckGroup.positiveUnit (typeF4RootPairing_baseEquiv 3) u =
      RootPairing.SimpleGeckGroup.positiveUnit (typeF4RootPairing_baseEquiv 3) u *
        RootPairing.SimpleGeckGroup.positiveUnit (typeF4RootPairing_baseEquiv 0) t from
      congrArg Subtype.val h.eq

private theorem same_root_commute (m : ℕ) (r : F4Chevalley.Root)
    (t u : CoefficientField m) :
    Commute (rootGeneratorInGroup m r t) (rootGeneratorInGroup m r u) := by
  apply Subtype.ext
  change F4Chevalley.rootCurve r t * F4Chevalley.rootCurve r u =
    F4Chevalley.rootCurve r u * F4Chevalley.rootCurve r t
  rw [← F4Chevalley.rootCurve_add, ← F4Chevalley.rootCurve_add, add_comm t u]

public theorem split_positive_linear_commutative (m : ℕ) :
    IsMulCommutative (splitSimpleBlock m .linear true) := by
  apply Subgroup.isMulCommutative_closure
  rintro x ⟨r, t, hr, rfl⟩ y ⟨s, u, hs, rfl⟩
  rcases positive_linear_root hr with rfl | rfl <;>
    rcases positive_linear_root hs with rfl | rfl
  · exact (same_root_commute m _ t u).eq
  · exact (end_roots_commute m t u).eq
  · exact (end_roots_commute m u t).symm.eq
  · exact (same_root_commute m _ t u).eq

public theorem positive_linear_commutative (m : ℕ) :
    IsMulCommutative (simpleBlock m .linear true) := by
  have := split_positive_linear_commutative m
  apply IsMulCommutative.of_setLike_mul_comm
  intro x hx y hy
  apply toSplitGroup_injective m
  simp only [map_mul]
  exact setLike_mul_comm (s := splitSimpleBlock m .linear true) hx hy

public theorem split_positive_linear_mul_self (m : ℕ) {x : SplitGroup m}
    (hx : x ∈ splitSimpleBlock m .linear true) : x * x = 1 := by
  have := split_positive_linear_commutative m
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, _, rfl⟩ := hx
    apply Subtype.ext
    change F4Chevalley.rootCurve r t * F4Chevalley.rootCurve r t = 1
    rw [← F4Chevalley.rootCurve_add, CharTwo.add_self_eq_zero, F4Chevalley.rootCurve_zero]
  | one => exact one_mul _
  | mul x y hx hy ihx ihy =>
    have hxy := setLike_mul_comm (s := splitSimpleBlock m .linear true) hx hy
    calc
      (x * y) * (x * y) = (x * x) * (y * y) := by
        rw [mul_assoc, ← mul_assoc y, ← hxy]
        simp only [mul_assoc]
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ih =>
    rw [← mul_inv_rev, ih, inv_one]

public theorem positive_linear_mul_self (m : ℕ) {x : Model m}
    (hx : x ∈ simpleBlock m .linear true) : x * x = 1 := by
  apply toSplitGroup_injective m
  rw [map_mul, map_one]
  exact split_positive_linear_mul_self m hx

end ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.LocalActions
