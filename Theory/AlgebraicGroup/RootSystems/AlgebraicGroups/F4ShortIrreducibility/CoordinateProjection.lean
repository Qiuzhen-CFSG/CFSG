module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ShortIrreducibility.InvariantSubspaces

/-!
# Coordinate projection in invariant F4 short subspaces

For a short simple root `i`, the second integral divided power restricts on the
short ideal to `x ↦ x(-i)eᵢ`. Indeed, the Cartan columns vanish, and if `j` is
short and `j + 2i` is a root, root lengths and integral pairings force `j = -i`.
The remaining opposite-root coefficient is one.

Composing this operator with the actual simple Tits lift gives projection onto
`eᵢ` in characteristic two. Root-curve invariance supplies divided-power and
Tits-word invariance. The root and Cartan column equations for Tits lifts then
transport this projection along the chosen Weyl route to every short root.
All operators act on the literal 52-coordinate integral Geck model.

Source: Steinberg, *Lectures on Chevalley Groups*, the integral divided-power
and admissible-lattice construction (`refs/KGroup/GLS3/Chapter2St1.tex`), as
formalized in `IntegralGeckConstruction` and `IntegralAllRootOperators`.
-/

public section

open scoped Classical Matrix
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4 ReeF4.WordRelations ReeF4.WordRelations.ShortOperators
open ReeF4.WordRelations.Faithfulness.RestrictedAdjoint

namespace Theory.AlgebraicGroup.F4Chevalley.ShortIrreducibility

private lemma short_two_step (i j s : Root) (hi : IsShortRoot i) (hj : IsShortRoot j)
    (h : typeF4RootPairing.root s =
      typeF4RootPairing.root j + (2 : ℕ) • typeF4RootPairing.root i) :
    letI := typeF4RootPairing.indexNeg
    j = -i := by
  let := typeF4RootPairing.indexNeg
  have hp : (typeF4RootPairing.pairingIn ℤ j i : ℝ) = 2 * dot j.val i.val := by
    change algebraMap ℤ ℝ _ = _
    rw [typeF4RootPairing.algebraMap_pairingIn, typeF4RootPairing_pairing,
      typeF4CorootScale_of_not_pair i hi]
  have hn : dot s.val s.val = 5 + 2 * (typeF4RootPairing.pairingIn ℤ j i : ℝ) := by
    change s.val = j.val + (2 : ℕ) • i.val at h
    rw [h]
    change (j.val + (2 : ℕ) • i.val) ⬝ᵥ (j.val + (2 : ℕ) • i.val) = _
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    rw [dotProduct_comm i.val j.val]
    change dot j.val j.val + 2 * dot j.val i.val +
      2 * (dot j.val i.val + 2 * dot i.val i.val) = _
    rw [isShortRoot_norm i hi, isShortRoot_norm j hj, hp]
    ring
  have hs : IsShortRoot s := by
    by_contra hs
    rw [isLongRoot_norm s (not_not.mp hs)] at hn
    have hz : 2 * typeF4RootPairing.pairingIn ℤ j i = -3 := by
      exact_mod_cast (show (2 : ℝ) * (typeF4RootPairing.pairingIn ℤ j i : ℝ) = -3 by linarith)
    omega
  rw [isShortRoot_norm s hs, hp] at hn
  have hz : j.val + i.val = 0 := by
    apply dotProduct_self_eq_zero.mp
    change dot (j.val + i.val) (j.val + i.val) = 0
    change (j.val + i.val) ⬝ᵥ (j.val + i.val) = 0
    rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm i.val j.val]
    change dot j.val j.val + dot j.val i.val + (dot j.val i.val + dot i.val i.val) = 0
    rw [isShortRoot_norm i hi, isShortRoot_norm j hj]
    linarith
  exact typeF4RootPairing.root_eq_neg_iff.mp (eq_neg_of_add_eq_zero_left hz)

private lemma simple_second_opposite (i : typeF4RootPairing_base.support) :
    letI := typeF4RootPairing.indexNeg
    eDividedPower (P := typeF4RootPairing) i 2 *ᵥ
      RootPairing.IntegralGeckConstruction.v (-i : Root) =
      RootPairing.IntegralGeckConstruction.v (i : Root) := by
  let := typeF4RootPairing.indexNeg
  have htop : typeF4RootPairing.chainTopCoeff i i = 0 :=
    typeF4RootPairing.chainTopCoeff_of_not_linearIndependent (by
      simp_rw [LinearIndependent.pair_iff, not_forall]
      exact ⟨1, -1, by simp, by simp⟩)
  simpa [htop] using eDividedPower_add_two_mulVec_v (P := typeF4RootPairing)
    (i := i) (j := (-i : Root)) (n := 0) (k := (i : Root)) (by
      rw [show typeF4RootPairing.root (-i : Root) = -typeF4RootPairing.root i from
        typeF4RootPairing.root_eq_neg_iff.mpr rfl]
      module)

variable {k : Type*} [Field k]

private lemma simple_second_short_column (i : typeF4RootPairing_base.support)
    (hi : IsShortRoot i.val) (j : BasisIndex) (hj : IsShortCoordinate j) :
    letI := typeF4RootPairing.indexNeg
    (eDividedPower (P := typeF4RootPairing) i 2).map (Int.castRingHom k) *ᵥ
      Pi.single j (1 : k) =
      if j = Sum.inr (-i : Root) then Pi.single (Sum.inr i.val) 1 else 0 := by
  let := typeF4RootPairing.indexNeg
  cases j with
  | inl j =>
    ext q
    have h := congrFun (eDividedPower_add_two_mulVec_u (P := typeF4RootPairing) i j 0) q
    simp only [u, Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] at h
    simp only [Sum.inl_ne_inr, ↓reduceIte, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.map_apply, h, map_zero, Pi.zero_apply]
  | inr j =>
    by_cases he : j = -i
    · subst j
      rw [if_pos rfl]
      ext q
      have h := congrFun (simple_second_opposite i) q
      simp only [v, Matrix.mulVec_single_one, Matrix.col_apply] at h
      simp only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply]
      rw [h]
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    · have hz : typeF4RootPairing.root j + (0 + 2) • typeF4RootPairing.root i ∉
          Set.range typeF4RootPairing.root := by
        rintro ⟨s, hs⟩
        exact he (short_two_step i j s hi hj hs)
      rw [if_neg (by simpa only [Sum.inr.injEq] using he)]
      ext q
      have h := congrFun (eDividedPower_add_two_mulVec_v_zero
        (P := typeF4RootPairing) i j 0 hz) q
      simp only [v, Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] at h
      simp only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply, h,
        map_zero, Pi.zero_apply]

private lemma simple_second_short (i : typeF4RootPairing_base.support)
    (hi : IsShortRoot i.val) {x : BasisIndex → k} (hx : ShortSupported x) :
    letI := typeF4RootPairing.indexNeg
    (eDividedPower (P := typeF4RootPairing) i 2).map (Int.castRingHom k) *ᵥ x =
      Pi.single (Sum.inr i.val) (x (Sum.inr (-i : Root))) := by
  let := typeF4RootPairing.indexNeg
  conv_lhs => rw [pi_eq_sum_univ' x]
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul]
  rw [Finset.sum_eq_single (Sum.inr (-i : Root))]
  · rw [simple_second_short_column i hi (Sum.inr (-i : Root))
      ((isShortRoot_neg_iff i.val).mpr hi), if_pos rfl]
    simp only [← Pi.single_smul, smul_eq_mul, mul_one]
  · intro j _ hj
    by_cases hs : IsShortCoordinate j
    · rw [simple_second_short_column i hi j hs, if_neg hj, smul_zero]
    · rw [hx j hs, zero_smul]
  · simp

private lemma titsLift_root_coordinate [CharP k 2]
    (i : typeF4RootPairing_base.support) (r : Root) (x : BasisIndex → k) :
    ((titsLift (P := typeF4RootPairing) i).map (Int.castRingHom k) *ᵥ x)
      (Sum.inr (typeF4RootPairing.reflectionPerm i r)) = x (Sum.inr r) := by
  have hentry (j : BasisIndex) :
      (titsLift (P := typeF4RootPairing) i).map (Int.castRingHom k)
        (Sum.inr (typeF4RootPairing.reflectionPerm i r)) j =
      if j = Sum.inr r then 1 else 0 := by
    cases j with
    | inl j =>
      have h := congrFun (titsLift_mulVec_u (P := typeF4RootPairing) i j)
        (Sum.inr (typeF4RootPairing.reflectionPerm i r))
      simp only [u, Matrix.mulVec_single_one, Matrix.col_apply] at h
      simp [Matrix.map_apply, h]
    | inr j =>
      have h := congrFun (titsLift_single (k := k) i j)
        (Sum.inr (typeF4RootPairing.reflectionPerm i r))
      simpa [Matrix.mulVec_single_one, Pi.single_apply, eq_comm] using h
  change ∑ j, _ * x j = _
  simp only [hentry]
  simp

private lemma simple_coordinate_mem [Infinite k] [CharP k 2]
    {W : Submodule k (BasisIndex → k)} (hW : RootCurveInvariant W)
    (hshort : W ≤ shortSubmodule) (i : typeF4RootPairing_base.support)
    (hi : IsShortRoot i.val) {x : BasisIndex → k} (hx : x ∈ W) :
    Pi.single (Sum.inr i.val : BasisIndex) (x (Sum.inr i.val)) ∈ W := by
  let := typeF4RootPairing.indexNeg
  let y := (titsLift (P := typeF4RootPairing) i).map (Int.castRingHom k) *ᵥ x
  have hy : y ∈ W := by
    simpa only [titsWord, Matrix.mul_one] using hW.titsWord_mem [i] hx
  have hmem := hW.dividedPower_mem i 2 hy
  rw [rootDividedPower_simple, simple_second_short i hi (hshort hy)] at hmem
  have hcoord : y (Sum.inr (-i : Root)) = x (Sum.inr i.val) :=
    titsLift_root_coordinate i i x
  rwa [hcoord] at hmem

private lemma reflection_coordinate_mem [CharP k 2]
    {W : Submodule k (BasisIndex → k)} (hW : RootCurveInvariant W)
    (r : Root)
    (hprojection : ∀ x ∈ W, Pi.single (Sum.inr r : BasisIndex) (x (Sum.inr r)) ∈ W)
    (i : typeF4RootPairing_base.support) {x : BasisIndex → k} (hx : x ∈ W) :
    Pi.single (Sum.inr (typeF4RootPairing.reflectionPerm i r) : BasisIndex)
      (x (Sum.inr (typeF4RootPairing.reflectionPerm i r))) ∈ W := by
  let y := (titsLift (P := typeF4RootPairing) i).map (Int.castRingHom k) *ᵥ x
  have hy : y ∈ W := by
    simpa only [titsWord, Matrix.mul_one] using hW.titsWord_mem [i] hx
  have hmem := hW.titsWord_mem [i] (hprojection y hy)
  have hsingle : Pi.single (Sum.inr r : BasisIndex) (y (Sum.inr r)) =
      y (Sum.inr r) • Pi.single (Sum.inr r) 1 := by
    simp only [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hsingle] at hmem
  simp only [titsWord, Matrix.mul_one, Matrix.mulVec_smul, titsLift_single] at hmem
  have hcoord : y (Sum.inr r) = x (Sum.inr (typeF4RootPairing.reflectionPerm i r)) := by
    simpa only [RootPairing.reflectionPerm_self] using
      titsLift_root_coordinate i (typeF4RootPairing.reflectionPerm i r) x
  simpa only [hcoord, ← Pi.single_smul, smul_eq_mul, mul_one] using hmem

/-- Every short-root coordinate projection preserves a root-curve invariant
subspace of the literal short ideal. -/
theorem RootCurveInvariant.root_coordinate_mem [IsAlgClosed k] [CharP k 2]
    {W : Submodule k (BasisIndex → k)} (hW : RootCurveInvariant W)
    (hshort : W ≤ shortSubmodule) {v : BasisIndex → k} (hv : v ∈ W)
    (r : Root) (hr : IsShortRoot r) :
    Pi.single (Sum.inr r : BasisIndex) (v (Sum.inr r)) ∈ W := by
  let route := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  have hi : IsShortRoot route.simple.val := by
    apply (isShortRoot_reflectionWord route.word route.simple).mp
    rwa [route.target]
  have hprojection : ∀ word : List typeF4RootPairing_base.support,
      ∀ y ∈ W, Pi.single (Sum.inr (reflectionWord word route.simple) : BasisIndex)
        (y (Sum.inr (reflectionWord word route.simple))) ∈ W := by
    intro word
    induction word with
    | nil => exact fun y hy => simple_coordinate_mem hW hshort route.simple hi hy
    | cons i word ih => exact fun y hy => reflection_coordinate_mem hW _ ih i hy
  simpa only [route.target] using hprojection route.word v hv

end Theory.AlgebraicGroup.F4Chevalley.ShortIrreducibility
