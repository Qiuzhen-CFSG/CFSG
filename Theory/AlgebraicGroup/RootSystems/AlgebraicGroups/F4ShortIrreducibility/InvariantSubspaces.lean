module
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ShortRepresentation
public import Theory.LinearAlgebra.PolynomialCoefficients
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators

/-!
# Invariant subspaces of the literal F4 short-ideal action

We work in the actual 52-coordinate integral Geck model. An invariant submodule
of the short representation embeds into these coordinates and is stable under
every root curve. Interpolation extracts all divided-power operators, including
in characteristic two. Actual Tits words transport root-coordinate vectors by
Weyl reflections; their integral signs disappear in characteristic two.

The existing zero-common-kernel and Cartan-column equations detect a short-root
line in a nonzero Cartan-supported subspace. Thus general detection reduces to
preservation of short-root coordinate projections. In the other direction, all
short-root lines generate the short ideal: opposite simple-root operators
supply the short Cartan coordinates.

The coordinate-projection and single-root generation assertions remain separate
obligations. None of these reductions assumes semisimplicity, a Borel subgroup,
or a highest-weight classification.

Source: Steinberg, *Lectures on Chevalley Groups*, integral admissible-lattice
construction (`refs/KGroup/GLS3/Chapter2St1.tex`), specialized to the literal F4
operators; GLS3 Remark 1.8.9 describes the Weyl geometry used in root generation.
-/

@[expose] public section
open scoped Matrix Classical
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4 ReeF4.WordRelations ReeF4.WordRelations.ShortOperators
open ReeF4.WordRelations.Faithfulness.RestrictedAdjoint
open ReeF4.BinaryDegree.ExceptionalTensor
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism

namespace Theory.AlgebraicGroup.F4Chevalley.ShortIrreducibility
variable {k : Type*} [Field k]

/-- Stability under every actual root curve on the ambient Geck coordinates. -/
def RootCurveInvariant (W : Submodule k (BasisIndex → k)) : Prop :=
  ∀ (r : Root) (t : k) (v : BasisIndex → k), v ∈ W →
    (rootCurve r t : Matrix BasisIndex BasisIndex k) *ᵥ v ∈ W

theorem RootCurveInvariant.dividedPower_mem [Infinite k]
    {W : Submodule k (BasisIndex → k)} (hW : RootCurveInvariant W)
    (r : Root) (n : ℕ) {v : BasisIndex → k} (hv : v ∈ W) :
    (integralOperators.rootDividedPower r n).map (Int.castRingHom k) *ᵥ v ∈ W := by
  by_cases hn : n < 4
  · let x : Fin 4 → k := fun i => Infinite.natEmbedding k i.val
    have hx : Function.Injective x := (Infinite.natEmbedding k).injective.comp Fin.val_injective
    apply W.coeff_mem_of_sum_pow_smul_mem
      (fun j : Fin 4 =>
        (integralOperators.rootDividedPower r j).map (Int.castRingHom k) *ᵥ v)
      x hx _ ⟨n, hn⟩
    intro i
    have h := hW r (x i) v hv
    rw [rootCurve_matrix_formula] at h
    simpa [Fin.sum_univ_four, dividedPower_zero, Matrix.add_mulVec,
      Matrix.smul_mulVec, specializeMatrix] using h
  · simp [dividedPower_eq_zero_of_four_le r n (by omega)]

theorem RootCurveInvariant.rootOperator_mem [Infinite k]
    {W : Submodule k (BasisIndex → k)} (hW : RootCurveInvariant W)
    (r : Root) {v : BasisIndex → k} (hv : v ∈ W) :
    (integralOperators.rootOperator r).map (Int.castRingHom k) *ᵥ v ∈ W := by
  simpa only [dividedPower_one] using hW.dividedPower_mem r 1 hv

/-- An invariant submodule of the short representation, viewed in all 52 coordinates. -/
def ambientImage (W : Submodule k (shortSubmodule (k := k))) :
    Submodule k (BasisIndex → k) := W.map shortSubmodule.subtype

theorem ambientImage_le (W : Submodule k (shortSubmodule (k := k))) :
    ambientImage W ≤ shortSubmodule := by
  rintro _ ⟨v, _, rfl⟩
  exact v.property

theorem ambientImage_invariant [IsAlgClosed k] [CharP k 2] {W : Submodule k (shortSubmodule (k := k))}
    (hW : IsInvariantSubmodule shortRepresentation W) :
    RootCurveInvariant (ambientImage W) := by
  rintro r t _ ⟨v, hv, rfl⟩
  refine ⟨(shortRepresentation.action (algebraicRootElement r t) :
    Module.End k shortSubmodule) v, hW _ _ hv, ?_⟩
  exact (shortRepresentation_apply _ v).trans (by rw [pointMatrix_root]; rfl)

theorem ambientImage_eq_bot_iff (W : Submodule k (shortSubmodule (k := k))) :
    ambientImage W = ⊥ ↔ W = ⊥ := by
  constructor
  · intro h
    apply Submodule.map_injective_of_injective
      (show Function.Injective shortSubmodule.subtype from Subtype.val_injective)
    simpa only [ambientImage, Submodule.map_bot] using h
  · rintro rfl
    exact Submodule.map_bot _

theorem ambientImage_eq_short_iff (W : Submodule k (shortSubmodule (k := k))) :
    ambientImage W = shortSubmodule ↔ W = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro v _
    have hv : (v : BasisIndex → k) ∈ ambientImage W := by rw [h]; exact v.property
    obtain ⟨w, hw, he⟩ := hv
    exact (Subtype.val_injective he : w = v) ▸ hw
  · rintro rfl
    exact (Submodule.map_top _).trans shortSubmodule.range_subtype

/-- Actual Tits words preserve every subspace stable under the root curves. -/
theorem RootCurveInvariant.titsWord_mem
    {W : Submodule k (BasisIndex → k)} (hW : RootCurveInvariant W)
    (word : List typeF4RootPairing_base.support)
    {v : BasisIndex → k} (hv : v ∈ W) :
    (titsWord (P := typeF4RootPairing) word).map (Int.castRingHom k) *ᵥ v ∈ W := by
  let := typeF4RootPairing.indexNeg
  induction word with
  | nil => simpa [titsWord] using hv
  | cons i word ih =>
    have he : rootCurveTitsWord (P := typeF4RootPairing) (S := k) (i :: word) =
        rootCurve (i : Root) 1 * rootCurve (-i : Root) (-1) * rootCurve (i : Root) 1 *
          rootCurveTitsWord word := by
      simp only [rootCurveTitsWord_cons, rootCurve, integralOperators,
        rootCurveUnit_simple, rootCurveUnit_neg_simple]
    change (rootCurveTitsWord (P := typeF4RootPairing) (S := k) (i :: word) :
      Matrix BasisIndex BasisIndex k) *ᵥ v ∈ W
    rw [he]
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact hW _ _ _ (hW _ _ _ (hW _ _ _ ih))

/-- The signs in the integral Tits root columns disappear in characteristic two. -/
theorem titsLift_single [CharP k 2]
    (i : typeF4RootPairing_base.support) (r : Root) :
    (titsLift (P := typeF4RootPairing) i).map (Int.castRingHom k) *ᵥ
        Pi.single (Sum.inr r : BasisIndex) (1 : k) =
      Pi.single (Sum.inr (typeF4RootPairing.reflectionPerm i r)) 1 := by
  let := typeF4RootPairing.indexNeg
  ext j
  have h := congrFun (titsLift_mulVec_v (P := typeF4RootPairing) i r) j
  simp only [v, Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply,
    smul_eq_mul] at h
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply]
  rw [h]
  simp [Pi.single_apply, CharTwo.neg_eq]

/-- A Tits word permutes the root-coordinate vectors by its reflection word. -/
theorem titsWord_single [CharP k 2]
    (word : List typeF4RootPairing_base.support) (r : Root) :
    (titsWord (P := typeF4RootPairing) word).map (Int.castRingHom k) *ᵥ
        Pi.single (Sum.inr r : BasisIndex) (1 : k) =
      Pi.single (Sum.inr (reflectionWord word r)) 1 := by
  induction word with
  | nil =>
    change (Matrix.map 1 (Int.castRingHom k)) *ᵥ _ = _
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    rfl
  | cons i word ih =>
    rw [titsWord, Matrix.map_mul, ← Matrix.mulVec_mulVec, ih, titsLift_single]
    rfl

/-- Membership of a root-coordinate line transports through actual Weyl actions. -/
theorem RootCurveInvariant.reflectionWord_single_mem [CharP k 2]
    {W : Submodule k (BasisIndex → k)} (hW : RootCurveInvariant W)
    (word : List typeF4RootPairing_base.support) (r : Root)
    (hr : Pi.single (Sum.inr r : BasisIndex) (1 : k) ∈ W) :
    Pi.single (Sum.inr (reflectionWord word r) : BasisIndex) (1 : k) ∈ W := by
  simpa only [titsWord_single] using hW.titsWord_mem word hr

/-- A root operator sends a Cartan-supported vector to its own root line. -/
theorem rootOperator_mulVec_of_rootCoordinates_zero [CharP k 2]
    (r : Root) (v : BasisIndex → k) (hv : ∀ s : Root, v (Sum.inr s) = 0) :
    (integralOperators.rootOperator r).map (Int.castRingHom k) *ᵥ v =
      (∑ j : typeF4RootPairing_base.support,
        v (Sum.inl j) * (typeF4RootPairing.pairingIn ℤ r j : k)) •
        Pi.single (Sum.inr r) 1 := by
  have hvsum : v = ∑ j : typeF4RootPairing_base.support,
      v (Sum.inl j) • Pi.single (Sum.inl j : BasisIndex) 1 := by
    ext i
    cases i with
    | inl i => simp [Pi.single_apply]
    | inr s => simp [hv s]
  conv_lhs => rw [hvsum]
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, rootOperator_cartanColumn, smul_smul]
  rw [Finset.sum_smul]

/-- The zero-common-kernel calculation eliminates the Cartan-only case. -/
theorem RootCurveInvariant.exists_root_single_of_cartan [Infinite k] [CharP k 2]
    {W : Submodule k (BasisIndex → k)} (hW : RootCurveInvariant W)
    {v : BasisIndex → k} (hv : v ∈ W) (hne : v ≠ 0)
    (hroot : ∀ s : Root, v (Sum.inr s) = 0) :
    ∃ r : Root, IsShortRoot r ∧ Pi.single (Sum.inr r : BasisIndex) (1 : k) ∈ W := by
  obtain ⟨r, hr, hrv⟩ : ∃ r : Root, IsShortRoot r ∧
      (integralOperators.rootOperator r).map (Int.castRingHom k) *ᵥ v ≠ 0 := by
    by_contra! h
    exact hne (rootOperator_commonKernel v h)
  let c : k := ∑ j : typeF4RootPairing_base.support,
    v (Sum.inl j) * (typeF4RootPairing.pairingIn ℤ r j : k)
  have he : (integralOperators.rootOperator r).map (Int.castRingHom k) *ᵥ v =
      c • Pi.single (Sum.inr r : BasisIndex) 1 :=
    rootOperator_mulVec_of_rootCoordinates_zero r v hroot
  have hc : c ≠ 0 := by
    intro hzero
    exact hrv (by rw [he, hzero, zero_smul])
  refine ⟨r, hr, ?_⟩
  have hmem := hW.rootOperator_mem r hv
  rw [he] at hmem
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using W.smul_mem c⁻¹ hmem

/-- Coordinate projection, together with the proved Cartan calculation, detects
an actual short-root line in every nonzero invariant short subspace. -/
theorem RootCurveInvariant.exists_root_single_of_projection [Infinite k] [CharP k 2]
    {W : Submodule k (BasisIndex → k)} (hW : RootCurveInvariant W)
    (hshort : W ≤ shortSubmodule) (hne : W ≠ ⊥)
    (hprojection : ∀ (v : BasisIndex → k), v ∈ W → ∀ r : Root,
      IsShortRoot r → Pi.single (Sum.inr r : BasisIndex) (v (Sum.inr r)) ∈ W) :
    ∃ r : Root, IsShortRoot r ∧ Pi.single (Sum.inr r : BasisIndex) (1 : k) ∈ W := by
  obtain ⟨v, hv, hvne⟩ := (Submodule.ne_bot_iff W).mp hne
  by_cases hroot : ∀ r : Root, v (Sum.inr r) = 0
  · exact hW.exists_root_single_of_cartan hv hvne hroot
  · push Not at hroot
    obtain ⟨r, hr⟩ := hroot
    have hs : IsShortRoot r := by
      by_contra hs
      exact hr (hshort hv (Sum.inr r) hs)
    refine ⟨r, hs, ?_⟩
    have hmem := W.smul_mem (v (Sum.inr r))⁻¹ (hprojection v hv r hs)
    simpa only [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hr] using hmem

/-- An opposite simple-root vector maps to the corresponding Cartan coordinate. -/
theorem simpleRootOperator_opposite_single
    (i : typeF4RootPairing_base.support) :
    letI := typeF4RootPairing.indexNeg
    (integralOperators.rootOperator i).map (Int.castRingHom k) *ᵥ
        Pi.single (Sum.inr (-i : Root) : BasisIndex) (1 : k) =
      Pi.single (Sum.inl i) 1 := by
  let := typeF4RootPairing.indexNeg
  change (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) i).map
    (Int.castRingHom k) *ᵥ _ = _
  rw [rootOperator_simple]
  ext j
  have h := congrFun (eMatrix_mulVec_v_neg (P := typeF4RootPairing) i) j
  simp only [v, u, Matrix.mulVec_single_one, Matrix.col_apply] at h
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply]
  rw [h]
  simp [Pi.single_apply]

/-- Once all short-root vectors lie in a stable subspace, the short Cartan
coordinates follow from the opposite-root equation, and together they span
exactly the short ideal. -/
theorem RootCurveInvariant.shortSubmodule_le_of_root_mem [Infinite k]
    {W : Submodule k (BasisIndex → k)} (hW : RootCurveInvariant W)
    (hroot : ∀ r : Root, IsShortRoot r →
      Pi.single (Sum.inr r : BasisIndex) (1 : k) ∈ W) :
    shortSubmodule ≤ W := by
  let := typeF4RootPairing.indexNeg
  have hcoord (j : BasisIndex) (hj : IsShortCoordinate j) : Pi.single j (1 : k) ∈ W := by
    cases j with
    | inl i =>
      have h := hW.rootOperator_mem i (hroot (-i) ((isShortRoot_neg_iff i.val).mpr hj))
      rwa [simpleRootOperator_opposite_single] at h
    | inr r => exact hroot r hj
  intro v hv
  change ShortSupported v at hv
  rw [pi_eq_sum_univ' v]
  apply W.sum_mem
  intro j _
  by_cases hj : IsShortCoordinate j
  · exact W.smul_mem _ (hcoord j hj)
  · rw [hv j hj, zero_smul]
    exact W.zero_mem

end Theory.AlgebraicGroup.F4Chevalley.ShortIrreducibility
