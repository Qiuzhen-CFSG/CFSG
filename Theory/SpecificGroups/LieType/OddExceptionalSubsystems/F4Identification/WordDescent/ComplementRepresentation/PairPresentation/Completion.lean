module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.LocalWords

/-!
# The literal F4 two-node completion

Quotient the signed simple-root word group by its published local relators.
The resulting group maps onto the actual Geck matrix cover. Each actual
pair subgroup embeds faithfully in this completion: its local identity words
are already among the defining relators, and evaluation is a left inverse.

These constructions supply the local subgroups used in the Curtis--Tits
argument, GLS3 §2.9.3 (`refs/KGroup/GLS3/chapter2.tex`). No global
injectivity, universal/adjoint comparison, or presentation theorem is assumed
or proved here.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation

variable (F : Type*) [Field F]

instance pairRelationSubgroup_normal : (pairRelationSubgroup F).Normal :=
  inferInstanceAs (Subgroup.normalClosure (pairRelators F)).Normal

/-- The universal completion of the literal two-node relations. -/
abbrev PairCompletion := Word F ⧸ pairRelationSubgroup F

def pairQuotient : Word F →* PairCompletion F :=
  QuotientGroup.mk' (pairRelationSubgroup F)

@[simp] theorem pairQuotient_eq_one_iff (w : Word F) :
    pairQuotient F w = 1 ↔ w ∈ pairRelationSubgroup F :=
  QuotientGroup.eq_one_iff w

def completionEvaluation : PairCompletion F →* Cover F :=
  QuotientGroup.lift (pairRelationSubgroup F) (coverEvaluation F)
    (pairRelationSubgroup_le F)

@[simp] theorem completionEvaluation_quotient (w : Word F) :
    completionEvaluation F (pairQuotient F w) = coverEvaluation F w := rfl

theorem completionEvaluation_surjective : Function.Surjective (completionEvaluation F) := by
  intro g
  obtain ⟨w, rfl⟩ := coverEvaluation_surjective F g
  exact ⟨pairQuotient F w, rfl⟩

/-- Every actual pair subgroup embeds in the completion, without a global
presentation assumption. -/
def pairEmbedding (i j : Fin 4) : pairSubgroup F i j →* PairCompletion F :=
  (pairEvaluationRange F i j).liftOfSurjective (pairEvaluationRange_surjective F i j)
    ⟨(pairQuotient F).comp (pairInclusion F i j), by
      intro v hv
      apply (pairQuotient_eq_one_iff F _).mpr
      apply Subgroup.subset_normalClosure
      exact ⟨i, j, v, congrArg Subtype.val hv, rfl⟩⟩

@[simp] theorem pairEmbedding_evaluation (i j : Fin 4) (v : PairWord F) :
    pairEmbedding F i j (pairEvaluationRange F i j v) =
      pairQuotient F (pairInclusion F i j v) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

@[simp] theorem pairEmbedding_generator (i j : Fin 4) (s k : Bool) (t : F) :
    pairEmbedding F i j (pairGenerator F i j s k t) =
      pairQuotient F (FreeGroup.of (s, pairNode i j k, t)) := by
  rw [pairGenerator, pairEmbedding_evaluation, pairInclusion_of]

@[simp] theorem completionEvaluation_pairEmbedding (i j : Fin 4)
    (g : pairSubgroup F i j) :
    completionEvaluation F (pairEmbedding F i j g) = g.val := by
  obtain ⟨v, rfl⟩ := pairEvaluationRange_surjective F i j g
  rw [pairEmbedding_evaluation, completionEvaluation_quotient]
  rfl

theorem pairEmbedding_injective (i j : Fin 4) :
    Function.Injective (pairEmbedding F i j) := by
  intro g h he
  apply Subtype.ext
  simpa only [completionEvaluation_pairEmbedding] using
    congrArg (completionEvaluation F) he

theorem presentation_iff_completionEvaluation_injective :
    (coverEvaluation F).ker = pairRelationSubgroup F ↔
      Function.Injective (completionEvaluation F) := by
  constructor
  · intro hp
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro g hg
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (pairRelationSubgroup F) g
    change pairQuotient F w = 1
    apply (pairQuotient_eq_one_iff F w).mpr
    rw [← hp]
    exact hg
  · intro hi
    apply le_antisymm _ (pairRelationSubgroup_le F)
    intro w hw
    apply (pairQuotient_eq_one_iff F w).mp
    apply hi
    change coverEvaluation F w = 1 at hw
    simpa only [completionEvaluation_quotient, map_one] using hw

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
