module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylWords
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.LinearCoordinates


/-!
# The relative linear Weyl word in its signed fixed blocks

The fixed end-root coordinates give the word `u(1) v(1) u(1)`.
Commuting the distinct end-node factors identifies this with the specified
split Weyl word `[0,3]`. Thus the actual fixed representative belongs to
the join of the two signed fixed linear blocks, for every parameter.

Source: GLS3, Table 2.4 type VI and 2.3.8, `refs/KGroup/GLS3/chapter2.tex`.
The commutation calculation follows the existing `TorusGeometry.linearWeyl_split`.
-/

@[expose] public section

noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open RootPairing.IntegralGeckConstruction LargeLocalSeeds Parabolics.Binary.FixedGeometry
open BlockParameters.FieldRecovery
variable {m : ℕ}
local instance linearWordRootNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem end_commute (p q : Bool) (t u : CoefficientField m) :
    Commute (rootGeneratorInGroup m (signedRoot p (typeF4SimpleRootIndex 0)) t)
      (rootGeneratorInGroup m (signedRoot q (typeF4SimpleRootIndex 3)) u) := by
  have hne : typeF4RootPairing_baseEquiv 0 ≠ typeF4RootPairing_baseEquiv 3 := by
    intro h
    have := typeF4RootPairing_baseEquiv.injective h
    contradiction
  have hc : typeF4RootPairing_base.cartanMatrix
      (typeF4RootPairing_baseEquiv 3) (typeF4RootPairing_baseEquiv 0) = 0 := by
    rw [typeF4RootPairing_base_cartan_apply]
    norm_num [typeF4CartanMatrix, Fin.ext_iff]
  apply Subtype.ext
  cases p <;> cases q
  all_goals
    simp only [signedRoot, Bool.false_eq_true, ↓reduceIte]
    change F4Chevalley.rootCurve _ t * F4Chevalley.rootCurve _ u =
      F4Chevalley.rootCurve _ u * F4Chevalley.rootCurve _ t
    simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
      ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple, rootCurveUnit_neg_simple]
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_negative_negative_of_cartan_eq_zero _ _ hne hc t u).eq
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_negative _ _ hne.symm u t).eq.symm
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_negative _ _ hne t u).eq
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_positive_of_cartan_eq_zero _ _ hne hc t u).eq


/-- The specified end-node Weyl lift is a three-factor signed fixed word. -/
theorem relativeWeyl_linear_eq (d : LocalBlockInput m) :
    relativeWeyl d .linear =
      linearElement d true 1 * linearElement d false 1 * linearElement d true 1 := by
  apply Subtype.ext
  simp only [relativeWeyl_val, Subgroup.coe_mul, linearElement_word]
  simp only [linearWord, linearRoots, signedRoot, Bool.false_eq_true, ↓reduceIte,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_one,
    simpleWord, sideWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, Parabolics.weylWord, inv_one, CharTwo.neg_eq]
  have h1 := (end_commute false true (1 : CoefficientField m) 1).symm
  have h2 := (end_commute true false (1 : CoefficientField m) 1).symm
  have h3 := (end_commute true true (1 : CoefficientField m) 1).symm
  simp only [signedRoot, Bool.false_eq_true, ↓reduceIte] at h1 h2 h3
  symm
  calc
    _ = (rootGeneratorInGroup m (typeF4SimpleRootIndex 0) 1 *
          rootGeneratorInGroup m (-typeF4SimpleRootIndex 0) 1) *
        ((rootGeneratorInGroup m (typeF4SimpleRootIndex 3) 1 *
          rootGeneratorInGroup m (-typeF4SimpleRootIndex 3) 1) *
        (rootGeneratorInGroup m (typeF4SimpleRootIndex 0) 1 *
          rootGeneratorInGroup m (typeF4SimpleRootIndex 3) 1)) := by
      simp only [mul_assoc]
      rw [h1.left_comm]
    _ = _ := by
      rw [(h3.mul_left h2).left_comm]
      simp only [mul_assoc]

/-- The end-node Weyl representative lies in its signed fixed blocks. -/
theorem relativeWeyl_linear_mem (d : LocalBlockInput m) :
    relativeWeyl d .linear ∈ simpleBlock d .linear true ⊔ simpleBlock d .linear false := by
  rw [relativeWeyl_linear_eq]
  exact mul_mem (mul_mem (mem_sup_left (linearElement_mem d true 1))
    (mem_sup_right (linearElement_mem d false 1))) (mem_sup_left (linearElement_mem d true 1))

end ReeF4.LocalBlockInput.PairRigidity.FixedCollection
