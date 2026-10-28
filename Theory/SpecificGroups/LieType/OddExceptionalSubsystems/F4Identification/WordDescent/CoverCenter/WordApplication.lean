module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent

/-!
# Application of the cover-center reduction to folded F4 words

The two adjoint-operator obligations discharge precisely the `hcenter` premise
of the existing block-representation descent theorem. Both block representations
remain the responsibility of the word-descent owner. This extension keeps the
cover-center argument independent of the importing word-descent assembly.

Sources: GLS3 §§2.2–2.6 and Aschbacher–Smith A.2.17, printed p.39.
-/

public section
noncomputable section

open Theory.AlgebraicGroup
open ReeF4.WordRelations.Faithfulness

namespace TwistedE6.FoldedSubsystem.F4Identification.CoverCenter
open WordDescent

variable (F : Type*) [Field F]

/-- Application to the actual two folded blocks, with only the two operator
obligations added to the parent's representation hypotheses. -/
theorem foldedEvaluation_eq_one_of_central_of_adjointMap
    (htwo : (2 : F) ≠ 0)
    (hinj : Function.Injective (adjointMap F))
    (heq : ∀ r t, Equivariant (adjointMap F) (F4Chevalley.rootCurve r t))
    (ρfixed : Cover F →* (fixedSpace F ≃ₗ[F] fixedSpace F))
    (ρcomplement : Cover F →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hfixed : ∀ (s : Bool) (i : Fin 4) (t : F),
      ρfixed (coverSimple F s i t) = eigenspaceAction F 1 (f4Simple F s i t))
    (hcomplement : ∀ (s : Bool) (i : Fin 4) (t : F),
      ρcomplement (coverSimple F s i t) = eigenspaceAction F (-1) (f4Simple F s i t))
    (w : Word F) (hw : coverEvaluation F w ∈ Subgroup.center (Cover F)) :
    foldedEvaluation F w = 1 :=
  foldedEvaluation_eq_one_of_central_of_blockRepresentations F htwo
    (center_eq_bot_of_adjointMap F htwo hinj heq)
    ρfixed ρcomplement hfixed hcomplement w hw

end TwistedE6.FoldedSubsystem.F4Identification.CoverCenter
