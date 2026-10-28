module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.Actions
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.LinearRigidity.OppositeWords
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.LinearRigidity.BraidParameters

public import Mathlib.GroupTheory.IsPerfect

/-!
# Signed field action on the Ree linear blocks

An automorphism preserving both type VI blocks induces additive parameter
maps `f` and `g`. The actual opposite-root braid relation, read on a
transverse two-dimensional root string, forces `f(t) * g(t⁻¹) = 1`.
Applying the automorphism to the Weyl conjugation formula then gives
`g(t⁻² * v) = f(t)⁻² * f(v)`. At `t = 1` this identifies the two signed
maps; since every element of the finite characteristic-two field is a
square, the general formula forces scaled multiplicativity of `f`.
Normalizing by `f(1)` produces the common field equivalence, with inverse
unit scales on the two signs.

The argument needs only preservation of the two blocks. The final wrapper
retains the supplied source hypotheses for the local Ree application.
Multiplication and the inverse scale are conclusions of the concrete
relations, not assumptions or consequences of an unproved identification.

Source: GLS3, Table 2.4 type VI, §2.4, and 2.5.1(b,c),
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
variable {m : ℕ}

private theorem linearParameter_ne_zero (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) (p : Bool) {t : CoefficientField m} (ht : t ≠ 0) :
    linearParameterAut d a hb p t ≠ 0 := by
  intro h
  apply ht
  exact (linearParameterAut d a hb p).injective (h.trans (map_zero (linearParameterAut d a hb p)).symm)

private theorem linearParameter_inverse (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) {t : CoefficientField m} (ht : t ≠ 0) :
    linearParameterAut d a hb false t⁻¹ = (linearParameterAut d a hb true t)⁻¹ := by
  have h := congrArg a (linearElement_braid d t ht)
  simp only [map_mul, linearParameterAut_action d a hb] at h
  have he := linearElement_braid_parameter d _ _ (linearParameter_ne_zero d a hb true ht) h
  exact eq_inv_of_mul_eq_one_right he

private theorem linearWeylWord_action (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) {t : CoefficientField m} (ht : t ≠ 0) :
    a (linearWeylWord d t) = linearWeylWord d (linearParameterAut d a hb true t) := by
  simp only [linearWeylWord, map_mul, linearParameterAut_action d a hb, linearParameter_inverse d a hb ht]

private theorem linearParameter_conjugation (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) {t : CoefficientField m} (ht : t ≠ 0) (v : CoefficientField m) :
    linearParameterAut d a hb false (t⁻¹ ^ 2 * v) =
      (linearParameterAut d a hb true t)⁻¹ ^ 2 * linearParameterAut d a hb true v := by
  have h := congrArg a (linearWeylWord_conj d t ht v)
  simp only [map_mul, map_inv, linearWeylWord_action d a hb ht, linearParameterAut_action d a hb] at h
  rw [linearWeylWord_conj d _ (linearParameter_ne_zero d a hb true ht)] at h
  exact (linearElement_injective d false h).symm

private theorem linearParameter_negative (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) (v : CoefficientField m) :
    linearParameterAut d a hb false v =
      (linearParameterAut d a hb true 1)⁻¹ ^ 2 * linearParameterAut d a hb true v := by
  simpa only [inv_one, one_pow, one_mul] using
    linearParameter_conjugation d a hb one_ne_zero v

/-- Opposite-root conjugation forces multiplication on the additive linear parameter map. -/
theorem linearParameter_scaled_multiplicative (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) (t v : CoefficientField m) :
    linearParameterAut d a hb true (t * v) * linearParameterAut d a hb true 1 =
      linearParameterAut d a hb true t * linearParameterAut d a hb true v := by
  let f := linearParameterAut d a hb true
  let g := linearParameterAut d a hb false
  obtain ⟨r, rfl⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := CoefficientField m)) t
  by_cases hr : r = 0
  · simp [hr]
  have hmap (v : CoefficientField m) : g (r ^ 2 * v) = (f r⁻¹)⁻¹ ^ 2 * f v := by
    simpa only [inv_inv] using linearParameter_conjugation d a hb (inv_ne_zero hr) v
  have hneg (v : CoefficientField m) : g v = (f 1)⁻¹ ^ 2 * f v := linearParameter_negative d a hb v
  have he : ((f 1)⁻¹ ^ 2 * f (r ^ 2 * v)) * f 1 =
      ((f 1)⁻¹ ^ 2 * f (r ^ 2)) * f v := by
    rw [← hneg, ← hneg, hmap]
    have h1 : g (r ^ 2) = (f r⁻¹)⁻¹ ^ 2 * f 1 := by simpa only [mul_one] using hmap 1
    rw [h1]
    ring
  apply mul_left_cancel₀ (pow_ne_zero 2 (inv_ne_zero (linearParameter_ne_zero d a hb true one_ne_zero)))
  simpa only [mul_assoc] using he

/-- Both signed linear blocks share a field automorphism and inverse unit scales. -/
theorem exists_signedLinearAction_of_preservesSimpleBlocks
    (d : LocalBlockInput m) (a : MulAut d.fixedGroup) (hb : PreservesSimpleBlocks d a) :
    ∃ (b : (CoefficientField m)ˣ) (σ : CoefficientField m ≃+* CoefficientField m),
      SignedLinearAction d a b σ := by
  let f := linearParameterAut d a hb true
  have h1 : f 1 ≠ 0 := linearParameter_ne_zero d a hb true one_ne_zero
  obtain ⟨σ, hσ⟩ := exists_fieldEquiv_of_scaled_multiplicative f
    (linearParameter_scaled_multiplicative d a hb)
  refine ⟨Units.mk0 (f 1) h1, σ, ?_⟩
  intro p t
  rw [linearParameterAut_action d a hb]
  apply congrArg (linearElement d p)
  cases p
  · rw [linearParameter_negative, hσ t]
    change (f 1)⁻¹ ^ 2 * (f 1 * σ t) = (f 1)⁻¹ * σ t
    field_simp
  · exact hσ t

/-- Field recovery for the type VI blocks under the source local hypotheses. -/
theorem exists_signedLinearAction (_hm : 1 ≤ m) (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup]
    (_hindex : Odd (LargeLocalSeeds.standardUnipotent d).index)
    (a : MulAut d.fixedGroup) (_hp : d.PreservesUnipotentPair a)
    (hb : PreservesSimpleBlocks d a) :
    ∃ (b : (CoefficientField m)ˣ) (σ : CoefficientField m ≃+* CoefficientField m),
      SignedLinearAction d a b σ :=
  exists_signedLinearAction_of_preservesSimpleBlocks d a hb

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery

end
