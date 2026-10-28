module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.Diagonal
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.Model

/-!
# From one marked E6 chain representation to the folded complement

The four elementary curves generate SL3, so a homomorphism carrying them to
the first E6 chain lands in that literal chain subgroup. Composing with the
proved diagonal action gives the complementary SL3 representation and its
exact marking. No separate range, surjectivity, or faithfulness hypothesis
is needed for this target comparison.

The marked E6 homomorphism remains an explicit input. `ShortA2` combines
this target representation with the independent faithful F4 model. Source:
GLS3 §2.6.2 and Aschbacher--Smith A.2.17, printed p.39. All characteristics,
including three, are admitted by this transport argument.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open WordDescent

variable (F : Type*) [Field F]

namespace ShortA2

variable (η : Model F →* splitCarrier F)
  (hη : ∀ (s k : Bool) (t : F),
    η (modelGenerator F s k t) = simpleRoot F s (leftNode k) t)

include hη in
/-- Marking and elementary generation give containment in the actual chain. -/
theorem model_mem_leftSubgroup (g : Model F) : η g ∈ leftSubgroup F := by
  have htop : (leftSubgroup F).comap η = ⊤ := by
    apply model_generates F
    intro s k t
    change η (modelGenerator F s k t) ∈ leftSubgroup F
    rw [hη]
    simpa only [leftGenerator_val] using (leftGenerator F s k t).property
  have hg : g ∈ (leftSubgroup F).comap η := by rw [htop]; trivial
  exact hg

/-- Restriction to the literal E6 chain, without an extra range assumption. -/
def modelToLeft : Model F →* leftSubgroup F :=
  η.codRestrict (leftSubgroup F) (model_mem_leftSubgroup F η hη)

@[simp] theorem modelToLeft_generator (s k : Bool) (t : F) :
    modelToLeft F η hη (modelGenerator F s k t) = leftGenerator F s k t := by
  apply Subtype.ext
  exact (hη s k t).trans (leftGenerator_val F s k t).symm

/-- Apply the constructed diagonal action to a marked first-chain model. -/
def modelComplementAction : Model F →* (complementSpace F ≃ₗ[F] complementSpace F) :=
  (complementAction F).comp (modelToLeft F η hη)

@[simp] theorem modelComplementAction_generator (s k : Bool) (t : F) :
    modelComplementAction F η hη (modelGenerator F s k t) =
      eigenspaceAction F (-1) (f4Simple F s (pairNode 2 3 k) t) := by
  rw [modelComplementAction, MonoidHom.comp_apply, modelToLeft_generator,
    complementAction_generator]

end ShortA2

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
