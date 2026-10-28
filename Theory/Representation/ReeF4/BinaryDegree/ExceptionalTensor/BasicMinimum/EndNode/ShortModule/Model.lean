module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ShortRepresentation
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ChevalleyCorootWords
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.HighestWeight
public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.TraceValues.Coordinates

/-!
# A highest vector in the characteristic-two F4 short module

The short-coordinate submodule of the integral Geck representation has at most
26 dimensions: the length-interchanging coordinate involution pairs its
coordinates with the complement among the 52 Cartan and root coordinates.
Its vector at the highest short root is fixed by every positive root curve.
Indeed, integral divided powers raise the root height, whereas this vector
already has maximal height among the short coordinates; characteristic-two
invariance kills the remaining coordinates. The actual coroot words act on it
with exponents `(0,0,0,1)`.

The action and its rationality are those of `F4Chevalley.shortRepresentation`.
These concrete facts supply the input to the cyclic simple-head construction
in `ShortModule`, without using highest-weight uniqueness.

Sources: GLS3, Section 1.14, especially Theorem 1.14.6(d) and Example 1.14.9(c),
and Definition 2.8.1(b); the Geck integral construction underlying the literal
F4 root curves. The dimension is the small end-node model used in the Ree case
on printed p.356 of `refs/quasithin.pdf`.
-/

public section

open scoped Classical Matrix
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4 ReeF4.WordRelations ReeF4.WordRelations.Faithfulness.RestrictedAdjoint
open ReeF4.BinaryDegree.ExceptionalTensor
set_option linter.unusedSectionVars false
namespace ReeF4.BinaryDegree.ExceptionalTensor.EndNode.ShortModel
noncomputable section

private def unitRoot (i : Fin 4) : F4Chevalley.Root :=
  ⟨basisVector i, Or.inl (Or.inr ⟨i, Or.inl rfl⟩)⟩

private lemma unitRoot_short (i : Fin 4) : IsShortRoot (unitRoot i) := by
  intro h
  have hh := isLongRoot_norm (unitRoot i) h
  norm_num [unitRoot, dot, basisVector, Pi.single_apply, Fin.sum_univ_four] at hh

private lemma pairing_unit (r : F4Chevalley.Root) (i : Fin 4) :
    (typeF4RootPairing.pairingIn ℤ r (unitRoot i) : ℝ) = 2 * r.val i := by
  change algebraMap ℤ ℝ _ = _
  rw [typeF4RootPairing.algebraMap_pairingIn, typeF4RootPairing_pairing,
    typeF4CorootScale_of_not_pair _ (unitRoot_short i)]
  simp [unitRoot, dot, basisVector, Pi.single_apply]

private def height (x : Vec 4) : ℝ := 8 * x 0 + 3 * x 1 + 2 * x 2 + x 3

private lemma height_add (x y : Vec 4) : height (x + y) = height x + height y := by
  simp only [height, Pi.add_apply]; ring

private lemma height_simple (i : Fin 4) : height (typeF4SimpleRoot i) = 1 := by
  fin_cases i <;> norm_num [height, typeF4SimpleRoot, basisVector, Pi.single_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

private lemma height_positive (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r) :
    0 < height r.val := by
  apply hr.induction_on_add
  · intro i hi
    obtain ⟨j, hj⟩ := typeF4RootPairing_baseEquiv.surjective ⟨i, hi⟩
    have hjv := congrArg (fun s : typeF4RootPairing_base.support => s.val) hj
    change typeF4SimpleRootIndex j = i at hjv
    subst i
    rw [typeF4SimpleRootIndex_val, height_simple]
    norm_num
  · intro i j k hk hi hj
    change k.val = i.val + j.val at hk
    obtain ⟨q, hq⟩ := typeF4RootPairing_baseEquiv.surjective ⟨j, hj⟩
    have hqv := congrArg (fun s : typeF4RootPairing_base.support => s.val) hq
    change typeF4SimpleRootIndex q = j at hqv
    subst j
    rw [hk, height_add, typeF4SimpleRootIndex_val, height_simple]
    linarith

private lemma height_short_le (r : F4Chevalley.Root) (hr : IsShortRoot r) :
    height r.val ≤ 8 := by
  rcases r with ⟨x, (hp | hu) | hh⟩
  · exact (hr hp).elim
  · obtain ⟨i, hi | hi⟩ := hu
    all_goals
      change height x ≤ 8
      rw [hi]
      fin_cases i <;> norm_num [height, basisVector, Pi.single_apply, Fin.ext_iff]
  · obtain ⟨ε, rfl⟩ := hh
    have h (i : Fin 4) : halfSignVector ε i ≤ 1 / 2 := by
      simp only [halfSignVector]
      split <;> norm_num
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    dsimp [height]
    linarith

private lemma short_card : Fintype.card {j : F4Chevalley.BasisIndex // IsShortCoordinate j} = 26 := by
  let e : {j : F4Chevalley.BasisIndex // IsShortCoordinate j} ≃
      {j : F4Chevalley.BasisIndex // ¬IsShortCoordinate j} :=
    { toFun := fun j => ⟨coordinatePermutation j.val, by
        simpa only [coordinatePermutation_short_iff, not_not] using j.property⟩
      invFun := fun j => ⟨coordinatePermutation j.val, (coordinatePermutation_short_iff _).mpr j.property⟩
      left_inv := fun j => Subtype.ext (coordinatePermutation_involutive j.val)
      right_inv := fun j => Subtype.ext (coordinatePermutation_involutive j.val) }
  have htotal : Fintype.card F4Chevalley.BasisIndex = 52 := by
    rw [Fintype.card_sum,
      ← Fintype.card_congr typeF4RootPairing_baseEquiv,
      ← Fintype.card_congr Cartan.FieldSeparation.TraceValues.rootEquiv]
    norm_num
  have he := Fintype.card_congr e
  have hsum := Fintype.card_subtype_compl (α := F4Chevalley.BasisIndex) IsShortCoordinate
  omega

variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
/-- Restriction to the 26 short coordinates is injective. -/
theorem short_finrank : Module.finrank F (F4Chevalley.shortSubmodule (k := F)) ≤ 26 := by
  let f : F4Chevalley.shortSubmodule (k := F) →ₗ[F]
      ({j : F4Chevalley.BasisIndex // IsShortCoordinate j} → F) :=
    { toFun := fun v j => v.val j.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    funext j
    by_cases hj : IsShortCoordinate j
    · exact congrFun h ⟨j, hj⟩
    · exact (v.property j hj).trans (w.property j hj).symm
  simpa only [Module.finrank_pi, short_card] using LinearMap.finrank_le_finrank_of_injective hf

private def coordinateVector : F4Chevalley.BasisIndex → Vec 4
  | .inl _ => 0
  | .inr r => r.val

private lemma coordinate_weight (j : F4Chevalley.BasisIndex) (i : Fin 4) :
    (chevalleyBasisWeight (P := typeF4RootPairing) j (unitRoot i) : ℝ) =
      2 * coordinateVector j i := by
  cases j with
  | inl j => simp [chevalleyBasisWeight, coordinateVector]
  | inr r => exact pairing_unit r i

private lemma dividedPower_highest_short_entry (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (n : ℕ) (hn : 0 < n)
    (j : F4Chevalley.BasisIndex) (hj : IsShortCoordinate j) :
    rootDividedPower (P := typeF4RootPairing) (b := typeF4RootPairing_base)
      r n j (Sum.inr (unitRoot 0)) = 0 := by
  by_contra hne
  have hg := rootDividedPower_isChevalleyHomogeneous
    (P := typeF4RootPairing) (b := typeF4RootPairing_base) r n j (Sum.inr (unitRoot 0)) hne
  have hc (i : Fin 4) : coordinateVector j i - basisVector 0 i = (n : ℝ) * r.val i := by
    have h : (chevalleyBasisWeight (P := typeF4RootPairing) j (unitRoot i) : ℝ) -
        (chevalleyBasisWeight (P := typeF4RootPairing) (b := typeF4RootPairing_base) (Sum.inr (unitRoot 0)) (unitRoot i) : ℝ) =
        (n : ℝ) * (typeF4RootPairing.pairingIn ℤ r (unitRoot i) : ℝ) := by
      exact_mod_cast hg (unitRoot i)
    rw [coordinate_weight, coordinate_weight, pairing_unit] at h
    change 2 * coordinateVector j i - 2 * basisVector 0 i = _ at h
    linarith
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  norm_num [basisVector, Pi.single_apply, Fin.ext_iff] at h0 h1 h2 h3
  have he : height (coordinateVector j) - 8 = (n : ℝ) * height r.val := by
    dsimp [height]
    nlinarith
  have hjh : height (coordinateVector j) ≤ 8 := by
    cases j with
    | inl j => norm_num [coordinateVector, height]
    | inr j => exact height_short_le j hj
  have hp := mul_pos (Nat.cast_pos.mpr hn : (0 : ℝ) < n) (height_positive r hr)
  linarith

/-- The coordinate vector at the highest short root, the first Euclidean unit root. -/
def highestVector : F4Chevalley.shortSubmodule (k := F) :=
  ⟨Pi.single (Sum.inr (unitRoot 0)) (1 : F), shortSupported_single _ (unitRoot_short 0)⟩

/-- The highest short-root coordinate is nonzero. -/
theorem highestVector_ne_zero : highestVector (F := F) ≠ 0 := by
  intro h
  have hh := congrFun (congrArg Subtype.val h) (Sum.inr (unitRoot 0))
  simp [highestVector] at hh

open Classification.Steinberg.Geometry.ExceptionalMorphism

/-- Every positive root curve fixes the highest short-root vector. -/
theorem highestVector_root (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (t : F) :
    ((F4Chevalley.shortRepresentation (k := F)).action (algebraicRootElement r t) :
      Module.End F (F4Chevalley.shortSubmodule (k := F))) highestVector = highestVector := by
  apply Subtype.ext
  funext j
  by_cases hj : IsShortCoordinate j
  · have he := congrFun (F4Chevalley.shortRepresentation_apply
        (algebraicRootElement r t) (highestVector (F := F))) j
    rw [pointMatrix_root] at he
    rw [he]
    change ((rootCurveMatrix F4Chevalley.integralOperators r t) *ᵥ
      Pi.single (Sum.inr (unitRoot 0)) (1 : F)) j = (Pi.single (Sum.inr (unitRoot 0)) (1 : F) : F4Chevalley.BasisIndex → F) j
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, rootCurveMatrix,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    change (1 : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F) j (Sum.inr (unitRoot 0)) +
      t * (rootDividedPower (P := typeF4RootPairing) (b := typeF4RootPairing_base) r 1 j (Sum.inr (unitRoot 0)) : F) +
      t ^ 2 * (rootDividedPower (P := typeF4RootPairing) (b := typeF4RootPairing_base) r 2 j (Sum.inr (unitRoot 0)) : F) +
      t ^ 3 * (rootDividedPower (P := typeF4RootPairing) (b := typeF4RootPairing_base) r 3 j (Sum.inr (unitRoot 0)) : F) = _
    rw [dividedPower_highest_short_entry r hr 1 (by decide) j hj,
      dividedPower_highest_short_entry r hr 2 (by decide) j hj,
      dividedPower_highest_short_entry r hr 3 (by decide) j hj]
    simp [Matrix.one_apply, Pi.single_apply]
  · exact (((F4Chevalley.shortRepresentation (k := F)).action (algebraicRootElement r t) :
        Module.End F (F4Chevalley.shortSubmodule (k := F))) (highestVector (F := F))).property j hj |>.trans
      ((highestVector (F := F)).property j hj).symm

private lemma highest_pairing (i : Fin 4) :
    typeF4RootPairing.pairingIn ℤ (unitRoot 0) (typeF4SimpleRootIndex i) =
      (basicCoefficient (0, 1) i : ℤ) := by
  apply Int.cast_injective (α := ℝ)
  change algebraMap ℤ ℝ _ = _
  rw [typeF4RootPairing.algebraMap_pairingIn, typeF4RootPairing_pairing,
    typeF4CorootScale_simpleRoot]
  have hd (x : Vec 4) : dot (basisVector 0) x = x 0 := by
    simp [dot, basisVector, Pi.single_apply]
  change (if i.val < 2 then 1 else 2) * dot (basisVector 0) (typeF4SimpleRoot i) = _
  rw [hd]
  fin_cases i <;> norm_num [typeF4SimpleRoot, basicCoefficient, Fin.ext_iff,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private lemma pointMatrix_coroot (i : typeF4RootPairing_base.support) (t : Fˣ) :
    pointMatrix (algebraicCorootElement i t) =
      integralChevalleyTorusElement (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter i t⁻¹) := by
  have hn (r : F4Chevalley.Root) (u : Fˣ) :
      pointMatrix (algebraicNElement r u) = F4Chevalley.matrixN r (u : F) := by
    simp only [algebraicNElement, map_mul, pointMatrix_root, F4Chevalley.matrixN]
  rw [algebraicCorootElement, map_mul, map_inv, hn, hn]
  simp only [Units.val_one]
  rw [← F4Chevalley.matrixN_neg_one]
  exact F4Chevalley.matrixH_simple i t

/-- The simple positive coroots have eigenvalues with exponents `(0,0,0,1)`. -/
theorem highestVector_coroot (i : Fin 4) (t : Fˣ) :
    ((F4Chevalley.shortRepresentation (k := F)).action
      (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
        Module.End F (F4Chevalley.shortSubmodule (k := F))) highestVector =
      ((t : F) ^ basicCoefficient (0, 1) i) • highestVector := by
  have ht : chevalleyBasisTorusUnit (P := typeF4RootPairing)
      (integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) t⁻¹)
      (Sum.inr (unitRoot 0)) = t ^ basicCoefficient (0, 1) i := by
    unfold chevalleyBasisTorusUnit integralChevalleySimpleCorootParameter
    rw [Finset.prod_eq_single (typeF4RootPairing_baseEquiv i)]
    · simp only [if_true, chevalleyBasisWeight, typeF4RootPairing_baseEquiv_val,
        highest_pairing]
      simp
    · intro j _ hj
      simp [hj]
    · simp
  apply Subtype.ext
  rw [F4Chevalley.shortRepresentation_apply]
  change (pointMatrix (algebraicCorootElement (typeF4RootPairing_baseEquiv i) t) :
    Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F) *ᵥ
    Pi.single (Sum.inr (unitRoot 0)) (1 : F) =
      ((t : F) ^ basicCoefficient (0, 1) i) • Pi.single (Sum.inr (unitRoot 0)) (1 : F)
  rw [pointMatrix_coroot]
  change (Matrix.diagonal fun a => (chevalleyBasisTorusUnit (P := typeF4RootPairing)
      (integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) t⁻¹) a : F)) *ᵥ
    Pi.single (Sum.inr (unitRoot 0)) (1 : F) = _
  ext j
  by_cases hj : j = Sum.inr (unitRoot 0)
  · subst j
    simp [ht]
  · simp [hj]

end
end ReeF4.BinaryDegree.ExceptionalTensor.EndNode.ShortModel
