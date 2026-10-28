module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.RootCurve
public import Theory.AlgebraicGroup.Borel.IntegralChevalleyTorusConjugation

/-!
# A scalar actor in the concrete fixed Suzuki seed

The middle-node coroot words belong to the split Suzuki seed because their
positive and negative root factors are among its generators. Pair their
parameters under the Ree field twist: the twist interchanges the two words,
and their commutation makes the product fixed.

We identify a coroot word with the inverse of the diagonal torus convention
used by `IntegralChevalleyTorusConjugation`. For a squared unit parameter,
this follows by conjugating the unit-parameter Weyl word by the diagonal
matrix and using the reflection of its coroot weight. Squared parameters
suffice: a nonidentity unit has nonidentity square in characteristic two.
The Cartan entries then give scalar `(u^2)⁻¹` on the paired end-root curve,
for conjugation in the convention `h * x * h⁻¹`.

Source: the twisted F₄ root construction underlying Aschbacher–Smith,
F.1.12(II)(i), printed pp.263–264 (PDF pp.274–275) of `refs/quasithin.pdf`.
This module supplies the scalar actor needed by the radical commutator
argument; normal generation of the radical is a separate result.
-/

@[expose] public section
noncomputable section
namespace ReeF4.Parabolics.OuterLocal.SuzukiCommutators

open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

private abbrev diag (m : ℕ) (i : Fin 4) (u : (CoefficientField m)ˣ) :=
  integralChevalleyTorusElement (P := typeF4RootPairing)
    (integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) u)

private theorem diag_tits (m : ℕ) (i : Fin 4) (u : (CoefficientField m)ˣ) :
    rootCurveTitsWord (S := CoefficientField m) [typeF4RootPairing_baseEquiv i] * diag m i u =
      (diag m i u)⁻¹ * rootCurveTitsWord (S := CoefficientField m)
        [typeF4RootPairing_baseEquiv i] := by
  apply Units.ext
  change specializeMatrix (titsWord [typeF4RootPairing_baseEquiv i]) * Matrix.diagonal _ =
    Matrix.diagonal _ * specializeMatrix (titsWord [typeF4RootPairing_baseEquiv i])
  simp only [titsWord, Matrix.mul_one]
  ext row col
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : titsLift (typeF4RootPairing_baseEquiv i) row col = 0
  · simp [specializeMatrix, hz]
  · have hw := titsLift_respectsChevalleyGrading (typeF4RootPairing_baseEquiv i)
      row col hz (typeF4SimpleRootIndex i)
    have hn : chevalleyBasisWeight (P := typeF4RootPairing) row (typeF4SimpleRootIndex i) =
        -chevalleyBasisWeight (P := typeF4RootPairing) col (typeF4SimpleRootIndex i) := by
      rw [hw]
      cases col with
      | inl j => simp [chevalleyBasisWeight]
      | inr j =>
        exact typeF4RootPairing.pairingIn_reflectionPerm_self_right ℤ j _
    have heval (a : F4Chevalley.BasisIndex) :
        chevalleyBasisTorusUnit (P := typeF4RootPairing)
          (integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) u) a =
        u ^ (-chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex i)) := by
      unfold chevalleyBasisTorusUnit integralChevalleySimpleCorootParameter
      rw [Finset.prod_eq_single (typeF4RootPairing_baseEquiv i)]
      · simp only [if_true, typeF4RootPairing_baseEquiv_val]
      · intro j _ hj
        simp [hj]
      · simp
    have hu : chevalleyBasisTorusUnit (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) u) col =
        (chevalleyBasisTorusUnit (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) u) row)⁻¹ := by
      rw [heval, heval, hn]
      simp

    rw [hu]
    exact mul_comm _ _

noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem diag_root (m : ℕ) (i : Fin 4) (u : (CoefficientField m)ˣ)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    (diag m i u)⁻¹ * F4Chevalley.rootCurve r t * diag m i u =
      F4Chevalley.rootCurve r
        (((u ^ typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i) :
          (CoefficientField m)ˣ) : CoefficientField m) * t) := by
  exact integralChevalleyRootCurve_simpleCoroot_conjugation
    (typeF4RootPairing_baseEquiv i) u r t

private theorem diag_mul (m : ℕ) (i : Fin 4) (u v : (CoefficientField m)ˣ) :
    diag m i (u * v) = diag m i u * diag m i v := by
  rw [diag, ← integralChevalleyTorusElement_mul]
  congr 1
  funext j
  simp only [integralChevalleySimpleCorootParameter, Pi.mul_apply]
  split_ifs <;> simp

private theorem weyl_one (m : ℕ) (i : Fin 4) :
    (weylWord m (typeF4SimpleRootIndex i) 1).val =
      rootCurveTitsWord (S := CoefficientField m) [typeF4RootPairing_baseEquiv i] := by
  rw [rootCurveTitsWord_cons, rootCurveTitsWord_nil, mul_one]
  change F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
    F4Chevalley.rootCurve _ 1 = _
  simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple, rootCurveUnit_neg_simple,
    inv_one]

private theorem weyl_neg_one (m : ℕ) (i : Fin 4) :
    weylWord m (typeF4SimpleRootIndex i) (-1) =
      (weylWord m (typeF4SimpleRootIndex i) 1)⁻¹ := by
  apply Subtype.ext
  change F4Chevalley.rootCurve _ (-1) * F4Chevalley.rootCurve _ (-(-1)⁻¹) *
      F4Chevalley.rootCurve _ (-1) =
    (F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
      F4Chevalley.rootCurve _ 1)⁻¹
  simp [mul_inv_rev, F4Chevalley.rootCurve_inv, mul_assoc]

private theorem weyl_square (m : ℕ) (i : Fin 4) (u : (CoefficientField m)ˣ) :
    (weylWord m (typeF4SimpleRootIndex i) (u ^ 2)).val =
      (diag m i u)⁻¹ * (weylWord m (typeF4SimpleRootIndex i) 1).val * diag m i u := by
  change F4Chevalley.rootCurve _ _ * F4Chevalley.rootCurve _ _ *
    F4Chevalley.rootCurve _ _ =
    (diag m i u)⁻¹ * (F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
    F4Chevalley.rootCurve _ 1) * diag m i u
  symm
  calc
    _ = ((diag m i u)⁻¹ * F4Chevalley.rootCurve (typeF4SimpleRootIndex i) 1 * diag m i u) *
        ((diag m i u)⁻¹ * F4Chevalley.rootCurve (-typeF4SimpleRootIndex i) (-1⁻¹) * diag m i u) *
        ((diag m i u)⁻¹ * F4Chevalley.rootCurve (typeF4SimpleRootIndex i) 1 * diag m i u) := by group
    _ = _ := by simp [diag_root]

private theorem torus_square (m : ℕ) (i : Fin 4) (u : (CoefficientField m)ˣ) :
    (torusWord m (typeF4SimpleRootIndex i) (u ^ 2)).val = (diag m i (u ^ 2))⁻¹ := by
  change (weylWord m _ (u ^ 2)).val * (weylWord m _ (-1)).val = _
  rw [weyl_square, weyl_neg_one]
  change (diag m i u)⁻¹ * (weylWord m _ 1).val * diag m i u *
    ((weylWord m _ 1).val)⁻¹ = _
  rw [weyl_one, mul_assoc (diag m i u)⁻¹, diag_tits]
  rw [pow_two, diag_mul, mul_inv_rev]
  group

private theorem torus_square_commute (m : ℕ) (i j : Fin 4)
    (u v : (CoefficientField m)ˣ) :
    Commute (torusWord m (typeF4SimpleRootIndex i) (u ^ 2))
      (torusWord m (typeF4SimpleRootIndex j) (v ^ 2)) := by
  apply Subtype.ext
  change (torusWord m _ (u ^ 2)).val * (torusWord m _ (v ^ 2)).val =
    (torusWord m _ (v ^ 2)).val * (torusWord m _ (u ^ 2)).val
  rw [torus_square, torus_square]
  apply Commute.inv_inv
  change diag m i (u ^ 2) * diag m j (v ^ 2) =
    diag m j (v ^ 2) * diag m i (u ^ 2)
  simp only [diag, ← integralChevalleyTorusElement_mul, mul_comm]

private theorem torus_square_root (m : ℕ) (i : Fin 4) (u : (CoefficientField m)ˣ)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    torusWord m (typeF4SimpleRootIndex i) (u ^ 2) * rootGeneratorInGroup m r t *
        (torusWord m (typeF4SimpleRootIndex i) (u ^ 2))⁻¹ =
      rootGeneratorInGroup m r
        ((((u ^ 2) ^ typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i) :
          (CoefficientField m)ˣ) : CoefficientField m) * t) := by
  apply Subtype.ext
  change (torusWord m _ (u ^ 2)).val * F4Chevalley.rootCurve _ _ *
    ((torusWord m _ (u ^ 2)).val)⁻¹ = _
  rw [torus_square, inv_inv]
  exact diag_root m i (u ^ 2) r t

open LargeLocalSeeds

/-- A paired product in the middle-node Levi torus, using squared unit parameters. -/
def middleTorusWord (m : ℕ) (u : (CoefficientField m)ˣ) : SplitGroup m :=
  torusWord m (typeF4SimpleRootIndex 1) (u ^ 2) *
    torusWord m (typeF4SimpleRootIndex 2)
      ((Units.map (rootFieldEnd m (typeF4SimpleRootIndex 1) :
        CoefficientField m →* CoefficientField m) u) ^ 2)

private theorem weylWord_mem_seed (m : ℕ) (i : Fin 4) (hi : i ∈ leviNodes .suzuki)
    (t : CoefficientField m) :
    weylWord m (typeF4SimpleRootIndex i) t ∈ splitSeed m .suzuki := by
  have hp (a : CoefficientField m) :
      rootGeneratorInGroup m (typeF4SimpleRootIndex i) a ∈ splitSeed m .suzuki :=
    Subgroup.subset_closure ⟨_, _, Or.inl
      (typeF4RootPairing_base.isPos_of_mem_support (typeF4RootPairing_baseEquiv i).property),
      rfl⟩
  have hn (a : CoefficientField m) :
      rootGeneratorInGroup m (-typeF4SimpleRootIndex i) a ∈ splitSeed m .suzuki :=
    Subgroup.subset_closure ⟨_, _, Or.inr ⟨i, hi, rfl⟩, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hp _) (hn _)) (hp _)

/-- Both rank-one torus words are built from generators of the actual split seed. -/
theorem middleTorusWord_mem_seed (m : ℕ) (u : (CoefficientField m)ˣ) :
    middleTorusWord m u ∈ splitSeed m .suzuki := by
  have ht (i : Fin 4) (hi : i ∈ leviNodes .suzuki) (v : (CoefficientField m)ˣ) :
      torusWord m (typeF4SimpleRootIndex i) v ∈ splitSeed m .suzuki :=
    Subgroup.mul_mem _ (weylWord_mem_seed m i hi _) (weylWord_mem_seed m i hi _)
  exact Subgroup.mul_mem _ (ht 1 (by simp [leviNodes]) _) (ht 2 (by simp [leviNodes]) _)

/-- The exceptional twist interchanges the two commuting middle torus factors. -/
theorem middleTorusWord_fixed {m : ℕ} (d : LocalBlockInput m)
    (u : (CoefficientField m)ˣ) : d.twist (middleTorusWord m u) = middleTorusWord m u := by
  have h1 : exceptionalRootPermutation (typeF4SimpleRootIndex 1) =
      typeF4SimpleRootIndex 2 := exceptionalRootPermutation_simple 1
  have h2 : exceptionalRootPermutation (typeF4SimpleRootIndex 2) =
      typeF4SimpleRootIndex 1 := exceptionalRootPermutation_simple 2
  have htwice : Units.map
      (rootFieldEnd m (typeF4SimpleRootIndex 2) : CoefficientField m →* CoefficientField m)
      (Units.map (rootFieldEnd m (typeF4SimpleRootIndex 1) :
        CoefficientField m →* CoefficientField m) u) = u := by
    apply Units.ext
    exact h1 ▸ RadicalCoordinates.rootFieldEnd_twice m (typeF4SimpleRootIndex 1) u.val
  rw [d.twist_eq_reeAutomorphism, reeAutomorphism_apply]
  simp only [middleTorusWord, map_mul, reeTwist_torusWord, h1, h2, map_pow]
  rw [htwice]
  exact (torus_square_commute m 1 2 u
    (Units.map (rootFieldEnd m (typeF4SimpleRootIndex 1) :
      CoefficientField m →* CoefficientField m) u)).eq.symm

/-- The middle torus actor as an element of the fixed Suzuki seed. -/
def middleTorusElement {m : ℕ} (d : LocalBlockInput m) (u : (CoefficientField m)ˣ) :
    standardSeed d .suzuki :=
  ⟨⟨middleTorusWord m u, middleTorusWord_fixed d u⟩, middleTorusWord_mem_seed m u⟩

private theorem end_middle_rootFieldEnd_eq (m : ℕ) :
    rootFieldEnd m (typeF4SimpleRootIndex 0) = rootFieldEnd m (typeF4SimpleRootIndex 1) := by
  have h0 : IsLongRoot (typeF4SimpleRootIndex 0) :=
    (typeF4SimpleRootIndex_mem_pair_iff 0).mpr (by decide)
  have h1 : IsLongRoot (typeF4SimpleRootIndex 1) :=
    (typeF4SimpleRootIndex_mem_pair_iff 1).mpr (by decide)
  simp only [rootFieldEnd, if_pos h0, if_pos h1]

private theorem middleTorusWord_root (m : ℕ) (u : (CoefficientField m)ˣ)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    middleTorusWord m u * rootGeneratorInGroup m r t * (middleTorusWord m u)⁻¹ =
      rootGeneratorInGroup m r
        ((((u ^ 2) ^ typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 1) :
          (CoefficientField m)ˣ) : CoefficientField m) *
        (((((Units.map (rootFieldEnd m (typeF4SimpleRootIndex 1) :
            CoefficientField m →* CoefficientField m) u) ^ 2) ^
            typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 2) :
          (CoefficientField m)ˣ) : CoefficientField m) * t)) := by
  unfold middleTorusWord
  rw [mul_inv_rev]
  calc
    _ = torusWord m (typeF4SimpleRootIndex 1) (u ^ 2) *
        (torusWord m (typeF4SimpleRootIndex 2)
          ((Units.map (rootFieldEnd m (typeF4SimpleRootIndex 1) :
            CoefficientField m →* CoefficientField m) u) ^ 2) * rootGeneratorInGroup m r t *
          (torusWord m (typeF4SimpleRootIndex 2)
            ((Units.map (rootFieldEnd m (typeF4SimpleRootIndex 1) :
              CoefficientField m →* CoefficientField m) u) ^ 2))⁻¹) *
        (torusWord m (typeF4SimpleRootIndex 1) (u ^ 2))⁻¹ := by group
    _ = _ := by rw [torus_square_root, torus_square_root]

/-- The inverse-square scalar is the character on the end-root curve, with
conjugation in the convention `h * x * h⁻¹`. -/
theorem middleTorusElement_scaling {m : ℕ} (d : LocalBlockInput m)
    (u : (CoefficientField m)ˣ) (t : CoefficientField m) :
    middleTorusElement d u * endRootElement d t * (middleTorusElement d u)⁻¹ =
      endRootElement d (((u : CoefficientField m) ^ 2)⁻¹ * t) := by
  apply Subtype.ext
  apply Subtype.ext
  change middleTorusWord m u * endRootWord m t * (middleTorusWord m u)⁻¹ = _
  unfold endRootWord
  calc
    _ = (middleTorusWord m u * rootGeneratorInGroup m (typeF4SimpleRootIndex 0) t *
          (middleTorusWord m u)⁻¹) *
        (middleTorusWord m u * rootGeneratorInGroup m (typeF4SimpleRootIndex 3)
          (rootFieldEnd m (typeF4SimpleRootIndex 0) t) * (middleTorusWord m u)⁻¹) := by group
    _ = _ := by
      rw [middleTorusWord_root, middleTorusWord_root]
      simp only [show ∀ i j, typeF4RootPairing.pairingIn ℤ (typeF4SimpleRootIndex i)
          (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j from
          fun i j => typeF4RootPairing_base_cartan_apply i j]
      norm_num [endRootWord, typeF4CartanMatrix, Fin.ext_iff, end_middle_rootFieldEnd_eq,
        map_mul, map_inv₀, map_pow]

/-- Over a coefficient field larger than two, the concrete Suzuki seed
contains an actor with a nonidentity scalar on the fixed end-root curve. -/
theorem exists_endRootElement_scaling {m : ℕ} (hm : 1 ≤ m) :
    ∃ (h : standardSeed (canonicalLocalBlockInput m) .suzuki) (c : CoefficientField m),
      c ≠ 1 ∧ ∀ t, h * endRootElement (canonicalLocalBlockInput m) t * h⁻¹ =
        endRootElement (canonicalLocalBlockInput m) (c * t) := by
  classical
  have hcard : 2 < Nat.card (CoefficientField m) := by
    rw [field_card]
    have h := Nat.pow_lt_pow_right (a := 2) (by omega) (show 1 < 2 * m + 1 by omega)
    simpa using h
  have : Nontrivial (CoefficientField m)ˣ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_units]
    omega)
  obtain ⟨u, hu⟩ := exists_ne (1 : (CoefficientField m)ˣ)
  refine ⟨middleTorusElement (canonicalLocalBlockInput m) u,
    ((u : CoefficientField m) ^ 2)⁻¹, ?_, middleTorusElement_scaling _ u⟩
  intro hc
  apply hu
  apply Units.ext
  have hs : (u : CoefficientField m) ^ 2 = 1 := inv_eq_one.mp hc
  rcases sq_eq_one_iff.mp hs with h | h
  · exact h
  · simpa only [CharTwo.neg_eq, Units.val_one] using h

end ReeF4.Parabolics.OuterLocal.SuzukiCommutators
