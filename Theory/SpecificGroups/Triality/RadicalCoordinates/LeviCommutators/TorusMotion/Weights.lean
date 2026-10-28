module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.Actors
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.TorusMotion.Scalars
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus

/-!
# The folded Levi torus weights on the radical roots

Compute the root-coroot pairings in the published D₄ ordering, then apply
the proved diagonal action on each Geck curve. Multiplying the three arms
coroot actions gives t/(F(t) F²(t)) and t F(t)/F²(t) on short orbits 1 and 2,
and inverse norm and norm on long roots 0 and 1. The central coroot gives
t⁻¹ and t on short orbits 0 and 1 and long roots 1 and 2.

These are equations in the actual split group for every root parameter.
The actors are the elementary lifts from `Actors`, whose descended elements
belong to the root-generated subsystem Levi. Conjugation is on the left,
as in the proved Geck diagonal formulas.

Source: GLS3 2.4.7(f), Table 2.4.7 and §2.6
(`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith F.1.12(II),
printed pp.263–264 (`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.RadicalCoordinates.LeviCommutators
open Parabolics ConcreteBruhat TorusCoordinates PositiveCoordinates
open Theory.AlgebraicGroup.StandardRootSystem

private def weightTable : Fin 12 → Fin 4 → ℤ :=
  ![![2, -1, 0, 0], ![0, -1, 2, 0], ![0, -1, 0, 2], ![-1, 2, -1, -1],
    ![1, 1, -1, -1], ![-1, 1, 1, -1], ![-1, 1, -1, 1],
    ![1, 0, 1, -1], ![-1, 0, 1, 1], ![1, 0, -1, 1],
    ![1, -1, 1, 1], ![0, 1, 0, 0]]

private theorem pairing_table (j : Fin 12) (i : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex j) (typeDSimpleRootIndex 2 i) =
      weightTable j i := by
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = (weightTable j i : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing]
  fin_cases j <;> fin_cases i <;>
    norm_num [weightTable, rootIndex, difference, sumRoot, typeDSimpleRootIndex,
      typeDRootEmbedding, typeDRootVector, basisVector, dot, Fin.sum_univ_succ]
  all_goals norm_num [Pi.single_apply, Fin.ext_iff]

private theorem torus_curve (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (t : (ExtensionField P)ˣ) (j : Fin 12) (u : ExtensionField P) :
    torusWord P i t * curve P j u * (torusWord P i t)⁻¹ =
      curve P j (t.val ^ weightTable j i * u) := by
  rw [torusWord_curve_conjugate P hp, pairing_table]

private theorem conjugate_product {G : Type*} [Group G] (g h x : G) :
    (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by group

private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group

private theorem arms_curve (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) (j : Fin 12) (u : ExtensionField P) :
    elementaryInclusion P (torusElementary P hp .arms t) * curve P j u *
      (elementaryInclusion P (torusElementary P hp .arms t))⁻¹ =
      curve P j (t.val ^ weightTable j 0 *
        ((fieldFrobenius P t.val) ^ weightTable j 2 *
          ((fieldFrobenius P (fieldFrobenius P t.val)) ^ weightTable j 3 * u))) := by
  simp only [torusElementary_arms_val, conjugate_product, torus_curve P hp]
  rfl

/-- The arms torus scales the short orbit (4,5,6) by t/(F(t) F²(t)). -/
theorem torus_arms_short_one_conjugate (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) (u : ExtensionField P) :
    elementaryInclusion P (torusElementary P hp .arms t) * shortSplit P 1 u *
      (elementaryInclusion P (torusElementary P hp .arms t))⁻¹ =
      shortSplit P 1 ((t.val / (fieldFrobenius P t.val *
        fieldFrobenius P (fieldFrobenius P t.val))) * u) := by
  simp only [shortSplit, conjugate_mul, arms_curve P hp]
  simp [shortPosition, weightTable, map_mul, fieldFrobenius_three,
    -fieldFrobenius_apply, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/-- The arms torus scales the short orbit (7,8,9) by t F(t)/F²(t). -/
theorem torus_arms_short_two_conjugate (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) (u : ExtensionField P) :
    elementaryInclusion P (torusElementary P hp .arms t) * shortSplit P 2 u *
      (elementaryInclusion P (torusElementary P hp .arms t))⁻¹ =
      shortSplit P 2 ((t.val * fieldFrobenius P t.val /
        fieldFrobenius P (fieldFrobenius P t.val)) * u) := by
  simp only [shortSplit, conjugate_mul, arms_curve P hp]
  simp [shortPosition, weightTable, map_mul, fieldFrobenius_three,
    -fieldFrobenius_apply, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/-- The arms torus scales the long root at position 3 by the inverse norm. -/
theorem torus_arms_long_zero_conjugate (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) (u : fixedField P) :
    elementaryInclusion P (torusElementary P hp .arms t) * longSplit P 0 u *
      (elementaryInclusion P (torusElementary P hp .arms t))⁻¹ =
      longSplit P 0 ((cubicNorm P t.val)⁻¹ * u) := by
  simp [longSplit, arms_curve P hp, longPosition, weightTable, cubicNorm,
    -fieldFrobenius_apply, mul_comm, mul_left_comm]

/-- The arms torus scales the long root at position 10 by the norm. -/
theorem torus_arms_long_one_conjugate (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) (u : fixedField P) :
    elementaryInclusion P (torusElementary P hp .arms t) * longSplit P 1 u *
      (elementaryInclusion P (torusElementary P hp .arms t))⁻¹ =
      longSplit P 1 (cubicNorm P t.val * u) := by
  simp [longSplit, arms_curve P hp, longPosition, weightTable, cubicNorm,
    -fieldFrobenius_apply, mul_assoc]

/-- The central torus scales the short orbit (0,1,2) by the inverse parameter. -/
theorem torus_central_short_zero_conjugate (P : Parameters) (hp : P.prime = 2)
    (t : (fixedField P)ˣ) (u : ExtensionField P) :
    elementaryInclusion P (torusElementary P hp .central t) * shortSplit P 0 u *
      (elementaryInclusion P (torusElementary P hp .central t))⁻¹ =
      shortSplit P 0 ((t.val.val)⁻¹ * u) := by
  have ht : fieldFrobenius P t.val.val = t.val.val := t.val.property
  simp only [torusElementary_central_val, shortSplit, conjugate_mul, torus_curve P hp]
  simp [shortPosition, weightTable, fixedUnit, map_mul, map_inv₀, ht,
    -fieldFrobenius_apply]

/-- The central torus scales the short orbit (4,5,6) by its parameter. -/
theorem torus_central_short_one_conjugate (P : Parameters) (hp : P.prime = 2)
    (t : (fixedField P)ˣ) (u : ExtensionField P) :
    elementaryInclusion P (torusElementary P hp .central t) * shortSplit P 1 u *
      (elementaryInclusion P (torusElementary P hp .central t))⁻¹ =
      shortSplit P 1 (t.val.val * u) := by
  have ht : fieldFrobenius P t.val.val = t.val.val := t.val.property
  simp only [torusElementary_central_val, shortSplit, conjugate_mul, torus_curve P hp]
  simp [shortPosition, weightTable, fixedUnit, map_mul, ht, -fieldFrobenius_apply]

/-- The central torus scales the long root at position 10 by the inverse parameter. -/
theorem torus_central_long_one_conjugate (P : Parameters) (hp : P.prime = 2)
    (t : (fixedField P)ˣ) (u : fixedField P) :
    elementaryInclusion P (torusElementary P hp .central t) * longSplit P 1 u *
      (elementaryInclusion P (torusElementary P hp .central t))⁻¹ =
      longSplit P 1 (t.val⁻¹ * u) := by
  simp [torusElementary_central_val, longSplit, torus_curve P hp,
    longPosition, weightTable, fixedUnit]

/-- The central torus scales the long root at position 11 by its parameter. -/
theorem torus_central_long_two_conjugate (P : Parameters) (hp : P.prime = 2)
    (t : (fixedField P)ˣ) (u : fixedField P) :
    elementaryInclusion P (torusElementary P hp .central t) * longSplit P 2 u *
      (elementaryInclusion P (torusElementary P hp .central t))⁻¹ =
      longSplit P 2 (t.val * u) := by
  simp [torusElementary_central_val, longSplit, torus_curve P hp,
    longPosition, weightTable, fixedUnit]
end Triality.Standard.RadicalCoordinates.LeviCommutators
