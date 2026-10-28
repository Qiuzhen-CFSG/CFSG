module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent

/-!
# Complementary local actions in the central-word consumer

The conditional two-node construction supplies precisely the complementary
representation and marked equations required by the existing block consumer.
The source presentation and local actions remain explicit here, as do the
independently owned fixed representation and cover-center theorem. This leaf
keeps the representation construction independent of the word-descent assembly.
Source: the folded inclusion in Aschbacher--Smith A.2.17, printed p.39, using
the subsystem and presentation arguments of GLS3 §§2.6 and 2.9.
-/

public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open WordDescent

variable (F : Type*) [Field F]

/-- Actual consumer application, conditional on the independent mathematical inputs. -/
theorem foldedEvaluation_eq_one_of_central_of_pairActions
    (htwo : (2 : F) ≠ 0) (hcenter : Subgroup.center (Cover F) = ⊥)
    (hpresentation : (coverEvaluation F).ker = pairRelationSubgroup F)
    (ρ : ∀ i j : Fin 4,
      pairSubgroup F i j →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hρ : ∀ (i j : Fin 4) (s k : Bool) (t : F),
      ρ i j (pairGenerator F i j s k t) =
        eigenspaceAction F (-1) (f4Simple F s (pairNode i j k) t))
    (ρfixed : Cover F →* (fixedSpace F ≃ₗ[F] fixedSpace F))
    (hfixed : ∀ (s : Bool) (i : Fin 4) (t : F),
      ρfixed (coverSimple F s i t) = eigenspaceAction F 1 (f4Simple F s i t))
    (w : Word F) (hw : coverEvaluation F w ∈ Subgroup.center (Cover F)) :
    foldedEvaluation F w = 1 :=
  foldedEvaluation_eq_one_of_central_of_blockRepresentations F htwo hcenter
    ρfixed (ofPairActions F hpresentation ρ hρ) hfixed
    (ofPairActions_simple F hpresentation ρ hρ) w hw

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
