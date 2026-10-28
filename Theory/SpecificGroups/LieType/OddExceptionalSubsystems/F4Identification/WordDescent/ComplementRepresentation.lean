module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.Words
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.Eigenspaces
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.LocalWords
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.Coordinates

/-!
# Assembly of complementary actions from literal two-node subgroups

Local homomorphisms on the actual two-node subgroups kill every corresponding
local relator. If those relators normally generate the source kernel, their
marked actions therefore descend to the F4 cover. The generator equations keep
both signs, the reversed node order in `f4Simple`, and the parameter unchanged.
`ComplementRepresentation.Application` applies the resulting action to the
existing central-word consumer, together with its independently supplied
fixed-space representation. This module does not import that consumer.

This is conditional assembly: the source presentation and the local
homomorphisms remain explicit mathematical obligations. No unconditional
complementary representation or F4 identification is claimed. The source
presentation is the concrete F4 case of GLS3 §2.9.3; the local actions require
the integral subsystem calculations of §§2.2--2.6. Both are needed for the
folded inclusion in Aschbacher--Smith A.2.17, printed p.39. None of the arguments
below assumes irreducibility, so the assembly includes characteristic three.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification
open WordDescent
namespace ComplementRepresentation

variable (F : Type*) [Field F]

/-- Construct the complementary representation once the source presentation and
all the actual local marked actions have been proved. -/
def ofPairActions
    (hpresentation : (coverEvaluation F).ker = pairRelationSubgroup F)
    (ρ : ∀ i j : Fin 4,
      pairSubgroup F i j →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hρ : ∀ (i j : Fin 4) (s k : Bool) (t : F),
      ρ i j (pairGenerator F i j s k t) =
        eigenspaceAction F (-1) (f4Simple F s (pairNode i j k) t)) :
    Cover F →* (complementSpace F ≃ₗ[F] complementSpace F) :=
  descendOfPairPresentation F hpresentation
    ((eigenspaceAction F (-1)).comp (foldedEvaluation F)) ρ (by
      intro i j s k t
      simpa only [MonoidHom.comp_apply, foldedEvaluation_of] using hρ i j s k t)

@[simp] theorem ofPairActions_evaluation
    (hpresentation : (coverEvaluation F).ker = pairRelationSubgroup F)
    (ρ : ∀ i j : Fin 4,
      pairSubgroup F i j →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hρ : ∀ (i j : Fin 4) (s k : Bool) (t : F),
      ρ i j (pairGenerator F i j s k t) =
        eigenspaceAction F (-1) (f4Simple F s (pairNode i j k) t)) (w : Word F) :
    ofPairActions F hpresentation ρ hρ (coverEvaluation F w) =
      eigenspaceAction F (-1) (foldedEvaluation F w) :=
  descendOfPairPresentation_evaluation F hpresentation _ _ _ w

/-- The exact signed, parameter-preserving equations required by `WordDescent`. -/
@[simp] theorem ofPairActions_simple
    (hpresentation : (coverEvaluation F).ker = pairRelationSubgroup F)
    (ρ : ∀ i j : Fin 4,
      pairSubgroup F i j →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hρ : ∀ (i j : Fin 4) (s k : Bool) (t : F),
      ρ i j (pairGenerator F i j s k t) =
        eigenspaceAction F (-1) (f4Simple F s (pairNode i j k) t))
    (s : Bool) (i : Fin 4) (t : F) :
    ofPairActions F hpresentation ρ hρ (coverSimple F s i t) =
      eigenspaceAction F (-1) (f4Simple F s i t) := by
  simpa only [coverEvaluation_of, foldedEvaluation_of] using
    ofPairActions_evaluation F hpresentation ρ hρ (FreeGroup.of (s, i, t))

/-- The marked equations determine at most one action of the actual cover. -/
theorem marked_unique
    (ρ τ : Cover F →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hρ : ∀ (s : Bool) (i : Fin 4) (t : F),
      ρ (coverSimple F s i t) = eigenspaceAction F (-1) (f4Simple F s i t))
    (hτ : ∀ (s : Bool) (i : Fin 4) (t : F),
      τ (coverSimple F s i t) = eigenspaceAction F (-1) (f4Simple F s i t)) : ρ = τ := by
  have htop : ρ.eqLocus τ = ⊤ := coverSimple_generates F _ fun s i t =>
    (hρ s i t).trans (hτ s i t).symm
  apply MonoidHom.ext
  intro g
  have hg : g ∈ ρ.eqLocus τ := by rw [htop]; trivial
  exact hg

/-- Sparse column identities suffice for all of the local marked equations. -/
theorem exists_of_pairActions_on_columns (htwo : (2 : F) ≠ 0)
    (hpresentation : (coverEvaluation F).ker = pairRelationSubgroup F)
    (ρ : ∀ i j : Fin 4,
      pairSubgroup F i j →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hcolumns : ∀ (i j : Fin 4) (s k : Bool) (t : F) (b a : Index),
      (ρ i j (pairGenerator F i j s k t) (antiVector F b) : Space F) a =
        foldedMatrix F (f4Simple F s (pairNode i j k) t) a b -
          foldedMatrix F (f4Simple F s (pairNode i j k) t) a
            (Theory.AlgebraicGroup.StandardRootSystem.typeE6PinnedIndexEquiv b)) :
    ∃ σ : Cover F →* (complementSpace F ≃ₗ[F] complementSpace F),
      ∀ (s : Bool) (i : Fin 4) (t : F),
        σ (coverSimple F s i t) = eigenspaceAction F (-1) (f4Simple F s i t) := by
  have hρ (i j : Fin 4) (s k : Bool) (t : F) :
      ρ i j (pairGenerator F i j s k t) =
        eigenspaceAction F (-1) (f4Simple F s (pairNode i j k) t) :=
    linearEquiv_eq_eigenspaceAction F htwo _ _ (hcolumns i j s k t)
  exact ⟨ofPairActions F hpresentation ρ hρ,
    ofPairActions_simple F hpresentation ρ hρ⟩

end ComplementRepresentation
end TwistedE6.FoldedSubsystem.F4Identification
