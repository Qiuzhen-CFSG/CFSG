module

public import Theory.Representation.AffineNine.CharacterOrbit
public import Theory.Representation.InvariantsBaseChange

/-!
# Binary affine-nine weight geometry

Over the algebraic closure of the binary field, the nine characters of the
translation group are indexed by the ternary dual plane.  The actual special
and full linear complements act transitively on its eight nonzero points.
Thus scalar extension of any faithful finite-dimensional binary representation
has a common positive dimension on those eight weights.  The zero weight is
the translation-invariant space, with no restriction on its dimension.

The coordinate lemmas retain the literal affine action, including translations,
for the orbit-representative fixed-space estimate in the direct proof of
Aschbacher--Smith, Lemma 15.4.10, printed p.1159.  No irreducible constituent or
representation classification is used.
-/

public section

noncomputable section

namespace Representation.AffineNine

open Matrix
open scoped MatrixGroups

theorem algebraicClosure_translation_card_ne_zero :
    (Nat.card Translation : algebraicClosureE9) ≠ 0 := by
  have hcard : Nat.card Translation = 9 := by
    change Nat.card Plane = 9
    rw [Nat.card_eq_fintype_card, card_plane]
  rw [hcard]
  intro hz
  exact (by decide : ¬ 2 ∣ 9)
    ((CharP.cast_eq_zero_iff algebraicClosureE9 2 9).mp hz)

section AlgebraicClosure

variable {V L : Type*} [Group L] [AddCommGroup V]
  [Module algebraicClosureE9 V] [FiniteDimensional algebraicClosureE9 V]
  (j : L →* LinearGroup)

/-- The nine actual character spaces, indexed by the dual ternary plane. -/
@[expose] def planeWeightSpace (rho : Representation algebraicClosureE9 (Affine j) V)
    (w : Plane) : Submodule algebraicClosureE9 V :=
  (translationRepresentation j rho).characterWeightSpace
    (algebraicClosureTranslationCharacterEquiv (Multiplicative.ofAdd w))

omit [FiniteDimensional algebraicClosureE9 V] in
theorem planeWeightSpace_independent
    (rho : Representation algebraicClosureE9 (Affine j) V) :
    iSupIndep (planeWeightSpace j rho) := by
  exact ((translationRepresentation j rho).characterWeightSpace_independent
    algebraicClosure_translation_card_ne_zero).comp
      (algebraicClosureTranslationCharacterEquiv.injective.comp Multiplicative.ofAdd.injective)

theorem iSup_planeWeightSpace_eq_top
    (rho : Representation algebraicClosureE9 (Affine j) V) :
    (⨆ w, planeWeightSpace j rho w) = ⊤ := by
  apply top_unique
  rw [← (translationRepresentation j rho).iSup_characterWeightSpace_eq_top
    algebraicClosure_translation_card_ne_zero]
  refine iSup_le fun χ => ?_
  obtain ⟨t, ht⟩ := algebraicClosureTranslationCharacterEquiv.surjective χ.val
  exact ht ▸ le_iSup (planeWeightSpace j rho) t.toAdd

theorem planeWeightSpace_zero
    (rho : Representation algebraicClosureE9 (Affine j) V) :
    planeWeightSpace j rho 0 = (translationRepresentation j rho).invariants := by
  simpa only [planeWeightSpace, ofAdd_zero, map_one] using
    characterWeightSpace_one_eq_invariants j rho

omit [FiniteDimensional algebraicClosureE9 V] in
theorem planeWeightSpace_finrank_nonzero
    (rho : Representation algebraicClosureE9 (Affine j) V)
    (u : UniformWeights j rho) (w : Plane) (hw : w ≠ 0) :
    Module.finrank algebraicClosureE9 (planeWeightSpace j rho w) = u.nontrivialDim := by
  apply u.nontrivial_finrank
  intro h
  apply hw
  exact Multiplicative.ofAdd.injective
    (algebraicClosureTranslationCharacterEquiv.injective
      (h.trans (map_one algebraicClosureTranslationCharacterEquiv).symm))

omit [FiniteDimensional algebraicClosureE9 V] in
/-- Every affine element transports weights by its actual linear part.  The
translation component acts within each weight and does not change the index. -/
theorem mem_planeWeightSpace_apply
    (rho : Representation algebraicClosureE9 (Affine j) V)
    (g : Affine j) (w : Plane) (v : V) (hv : v ∈ planeWeightSpace j rho w) :
    rho g v ∈ planeWeightSpace j rho (dualPerm (linearPart j g) w) := by
  let χ := algebraicClosureTranslationCharacterEquiv (Multiplicative.ofAdd w)
  have hc := algebraicClosureTranslationCharacterEquiv_equivariant (linearPart j g) w
  rw [planeWeightSpace, ← hc, characterWeightSpace, Submodule.mem_iInf]
  intro x
  rw [Module.End.mem_eigenspace_iff]
  let y := (naturalAction (linearPart j g)).symm x
  have hv' : ∀ t, (translationRepresentation j rho) t v = (χ t : algebraicClosureE9) • v := by
    simpa only [planeWeightSpace, characterWeightSpace, Submodule.mem_iInf,
      Module.End.mem_eigenspace_iff] using hv
  have hconj : g * SemidirectProduct.inl y * g⁻¹ = SemidirectProduct.inl x := by
    rw [conjugate_translation]
    simp [y]
  change rho (SemidirectProduct.inl x) (rho g v) =
    (χ y : algebraicClosureE9) • rho g v
  rw [← hconj]
  simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]
  change rho g ((translationRepresentation j rho) y v) = _
  rw [hv' y, map_smul]

/-- Uniformity for the actual full affine model, with the character comparison
and transitivity both discharged. -/
def full_algebraicClosure_uniformWeights
    (rho : Representation algebraicClosureE9 Full V) (hfaith : Function.Injective rho) :
    UniformWeights (MonoidHom.id LinearGroup) rho :=
  uniformWeights_of_transitive (MonoidHom.id LinearGroup) rho hfaith
    algebraicClosure_translation_card_ne_zero
    (characterTransitive_of_coordinates (MonoidHom.id LinearGroup)
      algebraicClosureFullCharacterCoordinates dualPerm_full_transitive)

/-- Uniformity for the actual special affine model; determinant-one matrices
already act transitively on all eight nontrivial translation characters. -/
def special_algebraicClosure_uniformWeights
    (rho : Representation algebraicClosureE9 Special V) (hfaith : Function.Injective rho) :
    UniformWeights (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup) rho :=
  uniformWeights_of_transitive (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup)
    rho hfaith algebraicClosure_translation_card_ne_zero
    (characterTransitive_of_coordinates (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup)
      algebraicClosureSpecialCharacterCoordinates dualPerm_special_transitive)

end AlgebraicClosure

section Binary

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A faithful binary representation of the full affine-nine model has eight
equally sized positive nontrivial weights after extension to the binary closure. -/
def full_binary_uniformWeights
    (rho : Representation (ZMod 2) Full V) (hfaith : Function.Injective rho) :
    UniformWeights (MonoidHom.id LinearGroup) (rho.extendScalars algebraicClosureE9) :=
  full_algebraicClosure_uniformWeights (rho.extendScalars algebraicClosureE9)
    ((extendScalars_faithful_iff algebraicClosureE9 rho).mp hfaith)

/-- The same weight theorem for the actual special affine-nine model. -/
def special_binary_uniformWeights
    (rho : Representation (ZMod 2) Special V) (hfaith : Function.Injective rho) :
    UniformWeights (SpecialLinearGroup.toGL : SpecialLinear →* LinearGroup)
      (rho.extendScalars algebraicClosureE9) :=
  special_algebraicClosure_uniformWeights (rho.extendScalars algebraicClosureE9)
    ((extendScalars_faithful_iff algebraicClosureE9 rho).mp hfaith)

/-- The zero weight retains precisely the original binary translation-fixed
dimension; it need not have the same dimension as a nonzero weight. -/
theorem finrank_planeWeightSpace_zero_extendScalars
    {L : Type*} [Group L] (j : L →* LinearGroup)
    (rho : Representation (ZMod 2) (Affine j) V) :
    Module.finrank algebraicClosureE9
        (planeWeightSpace j (rho.extendScalars algebraicClosureE9) 0) =
      Module.finrank (ZMod 2) (translationRepresentation j rho).invariants := by
  rw [planeWeightSpace_zero]
  exact finrank_invariants_extendScalars_eq_of_finite (translationRepresentation j rho)

end Binary

end Representation.AffineNine
