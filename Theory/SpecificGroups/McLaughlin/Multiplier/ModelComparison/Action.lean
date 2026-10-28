module

public import Theory.SpecificGroups.McLaughlin.Multiplier.Basic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL

/-!
# The marked action interface for the McLaughlin carrier comparison

The Leech triangle stabilizer acts faithfully on its 275 graph points.
A labelling transports this action to the same symmetric group as the literal
ATLAS carrier. Lifts of its two specified generators then embed the generated
carrier into the triangle stabilizer. This uses the actual actions, not a
recognition by graph parameters or group order.

Source conventions: ATLAS `McLG1-p275B0`, inverted for a left action, and
Gerald Höhn's Leech construction (ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`). The imported port retains its
license in `LICENSES/ATLAS.txt`. The generator lifts are not constructed here;
`qt-i01-mcl-generator-lifts` owns their construction.
-/

@[expose] public section
noncomputable section

namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison

open Atlas.Sporadic.McLaughlin (Model Points)
open Sporadic.LeechRelated.McL

/-- The faithful Leech action written in the supplied degree-275 labelling. -/
def labelledAction (e : Fin 275 ≃ Points) : Model →* Equiv.Perm (Fin 275) :=
  e.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom Model Points)

@[simp] theorem labelledAction_apply (e : Fin 275 ≃ Points) (g : Model) (x : Fin 275) :
    labelledAction e g x = e.symm (g • e x) := rfl

theorem labelledAction_injective (e : Fin 275 ≃ Points) :
    Function.Injective (labelledAction e) := by
  let := Atlas.Sporadic.McLaughlin.faithful
  intro g h he
  apply MulAction.toPerm_injective (β := Points)
  exact e.symm.permCongrHom.injective he

/-- Concrete generator lifts under one common labelling. The equations refer
exactly to the inverse-source permutations defining `Carrier`. -/
structure GeneratorLifts where
  pointEquiv : Fin 275 ≃ Points
  liftA : Model
  liftB : Model
  liftA_apply : ∀ x, liftA • pointEquiv x = pointEquiv (generatorA x)
  liftB_apply : ∀ x, liftB • pointEquiv x = pointEquiv (generatorB x)

namespace GeneratorLifts

variable (d : GeneratorLifts)

theorem labelledAction_liftA : labelledAction d.pointEquiv d.liftA = generatorA := by
  ext x
  simp only [labelledAction_apply, d.liftA_apply, Equiv.symm_apply_apply]

theorem labelledAction_liftB : labelledAction d.pointEquiv d.liftB = generatorB := by
  ext x
  simp only [labelledAction_apply, d.liftB_apply, Equiv.symm_apply_apply]

/-- Generator lifting extends to every element of the literal generated group. -/
theorem generated_le_range : generated ≤ (labelledAction d.pointEquiv).range := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · exact ⟨d.liftA, d.labelledAction_liftA⟩
  · have hg' : g = generatorB := Set.mem_singleton_iff.mp hg
    subst g
    exact ⟨d.liftB, d.labelledAction_liftB⟩

/-- Lift of every carrier element, using faithfulness to make the lift unique. -/
def carrierEmbedding : Carrier →* Model :=
  (MonoidHom.ofInjective (labelledAction_injective d.pointEquiv)).symm.toMonoidHom.comp
    (Subgroup.inclusion d.generated_le_range)

theorem carrierEmbedding_injective : Function.Injective d.carrierEmbedding :=
  (MonoidHom.ofInjective (labelledAction_injective d.pointEquiv)).symm.injective.comp
    (Subgroup.inclusion_injective d.generated_le_range)

/-- The embedding recovers the original permutation, not merely its conjugacy class. -/
theorem labelledAction_carrierEmbedding (g : Carrier) :
    labelledAction d.pointEquiv (d.carrierEmbedding g) = g.val := by
  exact MonoidHom.apply_ofInjective_symm
    (labelledAction_injective d.pointEquiv) (Subgroup.inclusion d.generated_le_range g)

/-- Equivariance for every element of the original carrier. -/
theorem carrierEmbedding_apply (g : Carrier) (x : Fin 275) :
    d.carrierEmbedding g • d.pointEquiv x = d.pointEquiv (g.val x) := by
  apply d.pointEquiv.symm.injective
  exact (congrArg (fun p : Equiv.Perm (Fin 275) => p x)
    (d.labelledAction_carrierEmbedding g)).trans (d.pointEquiv.symm_apply_apply _).symm

end GeneratorLifts
end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
