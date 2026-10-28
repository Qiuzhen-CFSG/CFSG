module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem

/-!
# The relative Ree rotation in the actual normalizer quotient

The product of the end-node and middle-node orbit words acts on the F₄ roots
with fourth power minus the identity and eighth power the identity. The faithful
word comparison in `UniformWords` transfers the latter relation to the matrix
lifts over every coefficient field. The former power cannot lie in the fixed
torus, because torus elements fix every root line. The actual Borel–normalizer
intersection is that torus, so the fourth power remains nonidentity in its
relative quotient.

The coordinate formulas extend the calculation in
`DerivedTits/BruhatBound/Geometry.lean`, leaving that binary calculation intact.
Source: GLS3 2.3.2(d), 2.3.4(a), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.MarkedWeyl
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics Parabolics.Binary.FixedGeometry LargeLocalSeeds
open Parabolics.Binary.FixedGeometry.BruhatCoverage.FixedWeyl
open RootPairing.IntegralGeckConstruction
open SectionGeometry.BNPair SectionGeometry.BNPair.QuotientGeometry
attribute [local instance] borel_inf_normalizerWords_normal

private def simpleVector (i : Fin 4) (v : Vec 4) : Vec 4 :=
  ![![v 0, v 2, v 1, v 3],
    ![v 0, v 1, v 3, v 2],
    ![v 0, v 1, v 2, -v 3],
    ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]] i

private theorem simple_reflection_coordinates (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      simpleVector i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ _) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [simpleVector, typeF4SimpleRoot, dot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

private def wordVector : List (Fin 4) → Vec 4 → Vec 4
  | [], v => v
  | i :: l, v => simpleVector i (wordVector l v)

private theorem rootWord_coordinates (l : List (Fin 4)) (r : F4Chevalley.Root) :
    (typeF4RootPairing.weylGroupToPerm (rootWord l) r).val = wordVector l r.val := by
  rw [rootWord, ← reflectionWord_eq_weylGroupToPerm]
  induction l with
  | nil => rfl
  | cons i l ih =>
    simpa only [List.map_cons, reflectionWord, typeF4RootPairing_baseEquiv_val,
      simple_reflection_coordinates, wordVector] using congrArg (simpleVector i) ih

private def rotationWord : List (Fin 4) := sideWord .linear ++ sideWord .suzuki

private def rotate (v : Vec 4) : Vec 4 :=
  ![(v 0 + v 1 - v 2 - v 3) / 2,
    (v 0 - v 1 - v 2 + v 3) / 2,
    (v 0 + v 1 + v 2 + v 3) / 2,
    (v 0 - v 1 + v 2 - v 3) / 2]

private theorem rotation_coordinates (r : F4Chevalley.Root) :
    (typeF4RootPairing.weylGroupToPerm (rootWord rotationWord) r).val = rotate r.val := by
  rw [rootWord_coordinates]
  ext j
  fin_cases j <;>
    norm_num [rotationWord, sideWord, wordVector, simpleVector, rotate,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

private theorem rotate_twice (v : Vec 4) :
    rotate (rotate v) = ![-v 2, -v 3, v 0, v 1] := by
  ext j
  fin_cases j <;>
    norm_num [rotate, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail] <;> ring

private theorem rotate_four (v : Vec 4) :
    rotate (rotate (rotate (rotate v))) = -v := by
  rw [rotate_twice, rotate_twice]
  ext j
  fin_cases j <;> simp

private theorem rotation_four_coordinates (r : F4Chevalley.Root) :
    (typeF4RootPairing.weylGroupToPerm (rootWord rotationWord ^ 4) r).val = -r.val := by
  rw [map_pow]
  simp only [pow_succ, pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    rotation_coordinates, rotate_four]

private theorem eighth_eq_one_of_fourth_neg (w : typeF4RootPairing.weylGroup)
    (h : ∀ r : F4Chevalley.Root,
      (typeF4RootPairing.weylGroupToPerm (w ^ 4) r).val = -r.val) : w ^ 8 = 1 := by
  apply weyl_perm_injective
  ext r : 1
  apply Subtype.ext
  rw [show (8 : ℕ) = 4 + 4 by decide, pow_add, map_mul, map_one]
  change (typeF4RootPairing.weylGroupToPerm (w ^ 4)
    (typeF4RootPairing.weylGroupToPerm (w ^ 4) r)).val = r.val
  rw [h, h, neg_neg]

private theorem rotation_eight : rootWord rotationWord ^ 8 = 1 :=
  eighth_eq_one_of_fourth_neg _ rotation_four_coordinates

private theorem rotation_four_ne_one : rootWord rotationWord ^ 4 ≠ 1 := by
  intro he
  have h := rotation_four_coordinates (typeF4SimpleRootIndex 0)
  rw [he, map_one] at h
  have h1 := congrFun h 1
  norm_num [typeF4SimpleRootIndex_val, typeF4SimpleRoot] at h1

private theorem simpleWord_power (m : ℕ) (l : List (Fin 4)) (k : ℕ) :
    simpleWord m (List.replicate k l).flatten = simpleWord m l ^ k := by
  induction k with
  | zero => simp [simpleWord]
  | succ k ih =>
    simp only [List.replicate_succ, List.flatten_cons, simpleWord_append, ih, pow_succ']

private theorem rootWord_power (l : List (Fin 4)) (k : ℕ) :
    rootWord (List.replicate k l).flatten = rootWord l ^ k := by
  induction k with
  | zero => simp [rootWord]
  | succ k ih =>
    simp only [List.replicate_succ, List.flatten_cons, rootWord_append, ih, pow_succ']

private theorem simpleWord_power_eq_one_iff (m : ℕ) (l : List (Fin 4)) (k : ℕ) :
    simpleWord m l ^ k = 1 ↔ rootWord l ^ k = 1 := by
  have h := simpleWord_eq_iff m (List.replicate k l).flatten []
  rw [simpleWord_power, rootWord_power] at h
  exact h

private theorem rotation_lift_eight (m : ℕ) :
    (weylLift m .linear * weylLift m .suzuki) ^ 8 = 1 := by
  apply toSplitGroup_injective m
  rw [map_pow, map_mul, map_one, toSplitGroup_weylLift, toSplitGroup_weylLift,
    ← simpleWord_append]
  exact (simpleWord_power_eq_one_iff m rotationWord 8).mpr rotation_eight

/-- The product of the two actual simple quotient classes has eighth power one. -/
theorem relativeRotation_pow_eight (m : ℕ) :
    (simpleReflection m .linear * simpleReflection m .suzuki) ^ 8 = 1 := by
  have h : (simpleLift m .linear * simpleLift m .suzuki) ^ 8 = 1 :=
    Subtype.ext (rotation_lift_eight m)
  have hh := congrArg (QuotientGroup.mk'
    ((borel m ⊓ normalizerWords m).subgroupOf (normalizerWords m))) h
  simpa only [map_pow, map_mul, map_one, simpleReflection] using hh

/-- The fourth power survives the relative torus quotient: it negates every root. -/
theorem relativeRotation_pow_four_ne_one (m : ℕ) :
    (simpleReflection m .linear * simpleReflection m .suzuki) ^ 4 ≠ 1 := by
  intro he
  have he' : QuotientGroup.mk' _ ((simpleLift m .linear * simpleLift m .suzuki) ^ 4) =
      (1 : WeylQuotient m) := by
    simpa only [map_pow, map_mul, simpleReflection] using he
  have ht : (weylLift m .linear * weylLift m .suzuki) ^ 4 ∈ fixedTorus m := by
    rw [← borel_inf_normalizerWords]
    exact (QuotientGroup.eq_one_iff
      ((simpleLift m .linear * simpleLift m .suzuki) ^ 4)).mp he'
  change toSplitGroup m ((weylLift m .linear * weylLift m .suzuki) ^ 4) ∈ splitTorus m at ht
  rw [map_pow, map_mul, toSplitGroup_weylLift, toSplitGroup_weylLift,
    ← simpleWord_append] at ht
  obtain ⟨c, hc⟩ := torus_rootMonomial ht
  have hm := simpleWord_rootMonomial m (List.replicate 4 rotationWord).flatten
  rw [simpleWord_power, rootWord_power] at hm
  have hp := monomial_perm_unique hm hc
  apply rotation_four_ne_one
  apply weyl_perm_injective
  exact hp.trans (map_one _).symm

end ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.MarkedWeyl
