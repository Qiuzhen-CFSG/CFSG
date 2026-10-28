module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.Transport
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.Coordinates
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.LongA2.Lattice
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.LongA2.FixedBlock

/-!
# Descent of the long A2 complementary action through the fixed block

The concrete injection in `LongA2.Lattice` carries an identity word on the
fixed diagram block to an identity on the complement, once its signed simple
intertwining is proved. The resulting kernel inclusion constructs an actual
homomorphism on `pairSubgroup F 0 1` with the original generator parameters.
The local intertwining and the fixed-block representation remain explicit;
this conditional construction does not assert that either has been supplied.

Sources: GLS3 §2.6.2, the common-lattice subsystem construction, and the F4
inclusions in Aschbacher--Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section

namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2
open WordDescent
variable (F : Type*) [Field F]

section Descent
variable (htwo : (2 : F) ≠ 0) (h : Intertwines F)
  (ρ : Cover F →* (fixedSpace F ≃ₗ[F] fixedSpace F))
  (hρ : ∀ (s : Bool) (i : Fin 4) (t : F),
    ρ (coverSimple F s i t) = eigenspaceAction F 1 (f4Simple F s i t))

include htwo h ρ hρ in
/-- A fixed-block identity forces the complementary identity on this pair. -/
theorem wordAction_eq_one_of_cover (w : PairWord F)
    (hw : pairEvaluation F 0 1 w = 1) : wordAction F (-1) w = 1 := by
  have he : ρ.comp (pairEvaluation F 0 1) = wordAction F 1 := by
    apply FreeGroup.ext_hom
    rintro ⟨s, k, t⟩
    simp only [MonoidHom.comp_apply, pairEvaluation_of, wordAction_of, hρ]
  have hf : wordAction F 1 w = 1 := by
    rw [← he, MonoidHom.comp_apply, hw, map_one]
  apply LinearEquiv.ext
  intro v
  apply toFixed_injective F htwo
  rw [word_intertwines F h, hf]
  rfl

/-- Pull back the complement action from word evaluation after proving its kernel
vanishes. This constructs a homomorphism on the actual pair subgroup. -/
def action : PairAction F 0 1 where
  hom := (pairEvaluationRange F 0 1).liftOfSurjective
    (pairEvaluationRange_surjective F 0 1)
    ⟨wordAction F (-1), by
      intro w hw
      apply wordAction_eq_one_of_cover F htwo h ρ hρ
      exact congrArg Subtype.val hw⟩
  map_generator s k t := by
    change (pairEvaluationRange F 0 1).liftOfSurjective _ _
      (pairEvaluationRange F 0 1 (FreeGroup.of (s, k, t))) = _
    rw [MonoidHom.liftOfRightInverse_comp_apply]
    exact wordAction_of F (-1) s k t

end Descent
end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2

namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2
open WordDescent AdjointRestriction Matrix
local instance : Fintype Theory.AlgebraicGroup.StandardRootSystem.typeF4Roots := Fintype.ofFinite _
variable (F : Type*) [Field F]

/-- Application to the actual common-lattice map. The three remaining inputs
are concrete geometry and matrix identities, not an assumed complementary action. -/
def actionOfIntegralComparison (htwo : (2 : F) ≠ 0) (h : Intertwines F)
    (hsurj : Function.Surjective (FixedBlock.comparison F))
    (hpoly : ∀ s i,
      foldedCurve (Polynomial ℤ) s i Polynomial.X * matrix (Polynomial ℤ) =
        matrix (Polynomial ℤ) * sourceCurve (Polynomial ℤ) s i Polynomial.X) :
    PairAction F 0 1 :=
  action F htwo h (FixedBlock.representation F hsurj)
    (FixedBlock.representation_simple F hsurj hpoly)

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2
