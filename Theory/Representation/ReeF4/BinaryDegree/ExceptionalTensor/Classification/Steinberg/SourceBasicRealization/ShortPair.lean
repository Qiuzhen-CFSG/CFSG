module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.ShortModule
import all Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.ShortModule.Model

/-!
# The two highest short coordinates of F4

The actual coordinates at β=e₁ and γ=(e₁+e₂+e₃+e₄)/2 have heights eight
and seven. Every other short coordinate has height at most seven. Integral
divided-power homogeneity therefore fixes β and sends γ into γ+Fβ under
positive root curves. Their direct coroot weights add to (0,0,1,0).

The internal import deliberately reuses the height and coroot-matrix lemmas
of the same native short-coordinate construction. No internal name occurs
in the exported equations. Source: GLS3 Section 1.14 and the Geck model.
-/

public noncomputable section
open scoped Classical Matrix
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4.WordRelations ReeF4.WordRelations.Faithfulness.RestrictedAdjoint
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization.ShortPair
open EndNode.ShortModel
open Geometry.ExceptionalMorphism

private def gammaRoot : F4Chevalley.Root :=
  ⟨halfSignVector (fun _ => true), Or.inr ⟨_, rfl⟩⟩

private theorem gamma_short : IsShortRoot gammaRoot := by
  intro h
  have hh := isLongRoot_norm gammaRoot h
  norm_num [gammaRoot, dot, halfSignVector, Fin.sum_univ_four] at hh

private theorem gamma_ne_beta : gammaRoot ≠ unitRoot 0 := by
  intro h
  have he := congrArg (fun r : F4Chevalley.Root => r.val 0) h
  norm_num [gammaRoot, halfSignVector, unitRoot, basisVector, Pi.single_apply] at he

private theorem height_short_except_beta (r : F4Chevalley.Root)
    (hr : IsShortRoot r) (hne : r ≠ unitRoot 0) : height r.val ≤ 7 := by
  rcases r with ⟨x, (hp | hu) | hh⟩
  · exact (hr hp).elim
  · obtain ⟨i, hi | hi⟩ := hu
    · subst x
      fin_cases i
      · exact (hne rfl).elim
      all_goals norm_num [height, basisVector, Pi.single_apply, Fin.ext_iff]
    · change height x ≤ 7
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

private theorem dividedPower_gamma_entry (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (n : ℕ) (hn : 0 < n)
    (j : F4Chevalley.BasisIndex) (hj : IsShortCoordinate j)
    (hjne : j ≠ Sum.inr (unitRoot 0)) :
    rootDividedPower (P := typeF4RootPairing) (b := typeF4RootPairing_base)
      r n j (Sum.inr gammaRoot) = 0 := by
  by_contra hne
  have hg := rootDividedPower_isChevalleyHomogeneous
    (P := typeF4RootPairing) (b := typeF4RootPairing_base) r n j (Sum.inr gammaRoot) hne
  have hc (i : Fin 4) : coordinateVector j i - (1 / 2 : ℝ) = (n : ℝ) * r.val i := by
    have h : (chevalleyBasisWeight (P := typeF4RootPairing) j (unitRoot i) : ℝ) -
        (chevalleyBasisWeight (P := typeF4RootPairing) (b := typeF4RootPairing_base)
          (Sum.inr gammaRoot) (unitRoot i) : ℝ) =
        (n : ℝ) * (typeF4RootPairing.pairingIn ℤ r (unitRoot i) : ℝ) := by
      exact_mod_cast hg (unitRoot i)
    rw [coordinate_weight, coordinate_weight, pairing_unit] at h
    change 2 * coordinateVector j i - 2 * (halfSignVector (fun _ => true) i) = _ at h
    norm_num [halfSignVector] at h
    linarith
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have he : height (coordinateVector j) - 7 = (n : ℝ) * height r.val := by
    dsimp [height]
    nlinarith
  have hjh : height (coordinateVector j) ≤ 7 := by
    cases j with
    | inl j => norm_num [coordinateVector, height]
    | inr j => exact height_short_except_beta j hj (fun h => hjne (congrArg Sum.inr h))
  have hp := mul_pos (Nat.cast_pos.mpr hn : (0 : ℝ) < n) (height_positive r hr)
  linarith

universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- The highest short-root vector in the actual rational short module. -/
def betaVector : F4Chevalley.shortSubmodule (k := F) := highestVector

/-- The next highest short coordinate. -/
def gammaVector : F4Chevalley.shortSubmodule (k := F) :=
  ⟨Pi.single (Sum.inr gammaRoot) (1 : F), shortSupported_single _ gamma_short⟩

theorem beta_root (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r) (t : F) :
    ((F4Chevalley.shortRepresentation (k := F)).action (algebraicRootElement r t) :
      Module.End F (F4Chevalley.shortSubmodule (k := F))) betaVector = betaVector :=
  highestVector_root r hr t

/-- Positive root curves raise the second vector only into the first. -/
theorem gamma_root (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r) (t : F) :
    ∃ a : F,
      ((F4Chevalley.shortRepresentation (k := F)).action (algebraicRootElement r t) :
        Module.End F (F4Chevalley.shortSubmodule (k := F))) gammaVector =
          gammaVector + a • betaVector := by
  let w := ((F4Chevalley.shortRepresentation (k := F)).action
    (algebraicRootElement r t) : Module.End F (F4Chevalley.shortSubmodule (k := F)))
      (gammaVector (F := F))
  refine ⟨w.val (Sum.inr (unitRoot 0)), ?_⟩
  apply Subtype.ext
  funext j
  by_cases hβ : j = Sum.inr (unitRoot 0)
  · subst j
    change w.val (Sum.inr (unitRoot 0)) = _
    simp [gammaVector, betaVector, highestVector, Ne.symm gamma_ne_beta]
  by_cases hj : IsShortCoordinate j
  · have he := congrFun (F4Chevalley.shortRepresentation_apply
        (algebraicRootElement r t) (gammaVector (F := F))) j
    rw [pointMatrix_root] at he
    rw [he]
    change ((rootCurveMatrix F4Chevalley.integralOperators r t) *ᵥ
      Pi.single (Sum.inr gammaRoot) (1 : F)) j = _
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, rootCurveMatrix,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    change (1 : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F) j (Sum.inr gammaRoot) +
      t * (rootDividedPower (P := typeF4RootPairing) (b := typeF4RootPairing_base)
        r 1 j (Sum.inr gammaRoot) : F) +
      t ^ 2 * (rootDividedPower (P := typeF4RootPairing) (b := typeF4RootPairing_base)
        r 2 j (Sum.inr gammaRoot) : F) +
      t ^ 3 * (rootDividedPower (P := typeF4RootPairing) (b := typeF4RootPairing_base)
        r 3 j (Sum.inr gammaRoot) : F) = _
    rw [dividedPower_gamma_entry r hr 1 (by decide) j hj hβ,
      dividedPower_gamma_entry r hr 2 (by decide) j hj hβ,
      dividedPower_gamma_entry r hr 3 (by decide) j hj hβ]
    simp [gammaVector, betaVector, highestVector, Matrix.one_apply, Pi.single_apply,
      hβ]
  · exact w.property j hj |>.trans
      ((gammaVector (F := F) + w.val (Sum.inr (unitRoot 0)) • betaVector).property j hj).symm

omit [IsAlgClosed F] [CharP F 2] in
/-- Coordinate functionals separate the two vectors. -/
theorem separating_forms :
    ∃ f g : F4Chevalley.shortSubmodule (k := F) →ₗ[F] F,
      f betaVector = 1 ∧ f gammaVector = 0 ∧
        g betaVector = 0 ∧ g gammaVector = 1 := by
  let f : F4Chevalley.shortSubmodule (k := F) →ₗ[F] F :=
    { toFun := fun v => v.val (Sum.inr (unitRoot 0))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let g : F4Chevalley.shortSubmodule (k := F) →ₗ[F] F :=
    { toFun := fun v => v.val (Sum.inr gammaRoot)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  refine ⟨f, g, ?_, ?_, ?_, ?_⟩ <;>
    simp [f, g, betaVector, highestVector, gammaVector, gamma_ne_beta, Ne.symm gamma_ne_beta]

@[expose] def gammaWeight : Fin 4 → ℤ := ![0, 0, 1, -1]

private theorem gamma_pairing (i : Fin 4) :
    typeF4RootPairing.pairingIn ℤ gammaRoot (typeF4SimpleRootIndex i) = gammaWeight i := by
  apply Int.cast_injective (α := ℝ)
  change algebraMap ℤ ℝ _ = _
  rw [typeF4RootPairing.algebraMap_pairingIn, typeF4RootPairing_pairing,
    typeF4CorootScale_simpleRoot]
  fin_cases i <;>
    norm_num [gammaRoot, halfSignVector, dot, Fin.sum_univ_four, typeF4SimpleRoot,
      gammaWeight, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

theorem beta_coroot (i : Fin 4) (t : Fˣ) :
    ((F4Chevalley.shortRepresentation (k := F)).action
      (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
        Module.End F (F4Chevalley.shortSubmodule (k := F))) betaVector =
      ((t : F) ^ basicCoefficient (0, 1) i) • betaVector :=
  highestVector_coroot i t

/-- The direct coroot exponents of γ are (0,0,1,−1). -/
theorem gamma_coroot (i : Fin 4) (t : Fˣ) :
    ((F4Chevalley.shortRepresentation (k := F)).action
      (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
        Module.End F (F4Chevalley.shortSubmodule (k := F))) gammaVector =
      ((t ^ gammaWeight i : Fˣ) : F) • gammaVector := by
  have ht : chevalleyBasisTorusUnit (P := typeF4RootPairing)
      (integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) t⁻¹)
      (Sum.inr gammaRoot) = t ^ gammaWeight i := by
    unfold chevalleyBasisTorusUnit integralChevalleySimpleCorootParameter
    rw [Finset.prod_eq_single (typeF4RootPairing_baseEquiv i)]
    · simp only [if_true, chevalleyBasisWeight, typeF4RootPairing_baseEquiv_val,
        gamma_pairing]
      simp
    · intro j _ hj
      simp [hj]
    · simp
  apply Subtype.ext
  rw [F4Chevalley.shortRepresentation_apply]
  change (pointMatrix (algebraicCorootElement (typeF4RootPairing_baseEquiv i) t) :
    Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F) *ᵥ
    Pi.single (Sum.inr gammaRoot) (1 : F) = _
  rw [pointMatrix_coroot]
  change (Matrix.diagonal fun a => (chevalleyBasisTorusUnit (P := typeF4RootPairing)
    (integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) t⁻¹) a : F)) *ᵥ
    Pi.single (Sum.inr gammaRoot) (1 : F) = _
  ext j
  by_cases hj : j = Sum.inr gammaRoot
  · subst j
    simp [ht, gammaVector]
  · simp [hj, gammaVector]

omit [IsAlgClosed F] [CharP F 2] in
/-- The two direct eigencharacters multiply to the λ₃ character. -/
theorem coroot_product (i : Fin 4) (t : Fˣ) :
    (t : F) ^ basicCoefficient (0, 1) i * ((t ^ gammaWeight i : Fˣ) : F) =
      (t : F) ^ basicCoefficient (1, 0) i := by
  fin_cases i <;> simp [basicCoefficient, gammaWeight]

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization.ShortPair
