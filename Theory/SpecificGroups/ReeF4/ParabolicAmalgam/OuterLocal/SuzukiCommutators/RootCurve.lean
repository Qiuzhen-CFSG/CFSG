module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.Coordinates
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup.Commutation

/-!
# An additive fixed root curve in the Suzuki-side Ree radical

The two end nodes of the F₄ diagram are orthogonal and interchanged by the
exceptional twist. Their commuting root elements, with paired field
parameters, give an additive curve in the actual twist-fixed matrix group.
Both roots are outside the middle-node Levi subsystem, so the curve lies
in the root-defined Suzuki radical. These are membership and group-law
calculations; normal generation of the whole fixed radical is a separate
obligation.

The proof uses integral simple-root commutation and the explicit exceptional
root formula. Source: the standard twisted F₄ root construction underlying
Aschbacher–Smith, F.1.12(I)(5) and (II)(i), printed pp.263–264 (PDF pp.274–275)
of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.Parabolics.OuterLocal.SuzukiCommutators

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction LargeLocalSeeds

private theorem endRoots_commute (m : ℕ) (t u : CoefficientField m) :
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

/-- The product of the two positive end-root matrices with twist-compatible parameters. -/
def endRootWord (m : ℕ) (t : CoefficientField m) : SplitGroup m :=
  rootGeneratorInGroup m (typeF4SimpleRootIndex 0) t *
    rootGeneratorInGroup m (typeF4SimpleRootIndex 3)
      (rootFieldEnd m (typeF4SimpleRootIndex 0) t)

private theorem simple_radical (i : Fin 4) (hi : i = 0 ∨ i = 3) :
    IsRadicalRoot .suzuki (typeF4SimpleRootIndex i) := by
  refine ⟨typeF4RootPairing_base.isPos_of_mem_support
    (typeF4RootPairing_baseEquiv i).property, i, ?_, ?_⟩
  · rcases hi with rfl | rfl <;> simp [leviNodes]
  · rcases hi with rfl | rfl <;>
      norm_num [typeF4SimpleCoefficient, typeF4SimpleRoot, basisVector]

/-- Each factor belongs to the split Suzuki radical. -/
theorem endRootWord_mem_radical (m : ℕ) (t : CoefficientField m) :
    endRootWord m t ∈ splitRadical m .suzuki := by
  exact Subgroup.mul_mem _
    (Subgroup.subset_closure ⟨_, _, simple_radical 0 (Or.inl rfl), rfl⟩)
    (Subgroup.subset_closure ⟨_, _, simple_radical 3 (Or.inr rfl), rfl⟩)

/-- Commutation of the end roots makes their paired product twist-fixed. -/
theorem endRootWord_fixed {m : ℕ} (d : LocalBlockInput m) (t : CoefficientField m) :
    d.twist (endRootWord m t) = endRootWord m t := by
  have h0 : exceptionalRootPermutation (typeF4SimpleRootIndex 0) =
      typeF4SimpleRootIndex 3 := exceptionalRootPermutation_simple 0
  have h3 : exceptionalRootPermutation (typeF4SimpleRootIndex 3) =
      typeF4SimpleRootIndex 0 := exceptionalRootPermutation_simple 3
  have htwice := RadicalCoordinates.rootFieldEnd_twice m (typeF4SimpleRootIndex 0) t
  rw [h0] at htwice
  simp only [endRootWord, map_mul, d.twist_root, ← rootFieldEnd_apply, h0, h3, htwice]
  exact (endRoots_commute m t _).eq.symm

/-- The paired root word is an additive one-parameter curve. -/
theorem endRootWord_add (m : ℕ) (t u : CoefficientField m) :
    endRootWord m (t + u) = endRootWord m t * endRootWord m u := by
  have hadd (r : F4Chevalley.Root) (a b : CoefficientField m) :
      rootGeneratorInGroup m r (a + b) =
        rootGeneratorInGroup m r a * rootGeneratorInGroup m r b :=
    Subtype.ext (F4Chevalley.rootCurve_add r a b)
  simp only [endRootWord, map_add, hadd]
  rw [mul_assoc, ← mul_assoc (rootGeneratorInGroup m (typeF4SimpleRootIndex 0) u),
    (endRoots_commute m u _).eq, mul_assoc, ← mul_assoc]

/-- The paired curve inside the actual fixed Suzuki seed. -/
def endRootElement {m : ℕ} (d : LocalBlockInput m) (t : CoefficientField m) :
    standardSeed d .suzuki :=
  ⟨⟨endRootWord m t, endRootWord_fixed d t⟩,
    (splitRadical_le_unipotent m .suzuki).trans (splitUnipotent_le_splitSeed m .suzuki)
      (endRootWord_mem_radical m t)⟩

@[simp] theorem endRootElement_coe {m : ℕ} (d : LocalBlockInput m)
    (t : CoefficientField m) : (endRootElement d t).val.val = endRootWord m t := rfl

/-- Membership in the root-defined radical, relative to the fixed seed. -/
theorem endRootElement_mem_radical {m : ℕ} (d : LocalBlockInput m)
    (t : CoefficientField m) : endRootElement d t ∈ seedRadical d .suzuki :=
  endRootWord_mem_radical m t

theorem endRootElement_add {m : ℕ} (d : LocalBlockInput m) (t u : CoefficientField m) :
    endRootElement d (t + u) = endRootElement d t * endRootElement d u :=
  Subtype.ext (Subtype.ext (endRootWord_add m t u))

@[simp] theorem endRootElement_zero {m : ℕ} (d : LocalBlockInput m) :
    endRootElement d 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change F4Chevalley.rootCurve _ 0 *
    F4Chevalley.rootCurve _ (rootFieldEnd m _ 0) = 1
  simp

theorem endRootElement_neg {m : ℕ} (d : LocalBlockInput m) (t : CoefficientField m) :
    endRootElement d (-t) = (endRootElement d t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← endRootElement_add, neg_add_cancel, endRootElement_zero]

end ReeF4.Parabolics.OuterLocal.SuzukiCommutators
