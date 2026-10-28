module
public import Theory.GroupTheory.SmallKernelPerfectFactorization
public import Theory.SpecificGroups.Janko3.Model.Perfect
public import Theory.SpecificGroups.Janko3.Model.Order

/-!
# Factoring a bounded cover through the concrete J₃ model

A finite group mapping onto both the concrete model and a centerless target
has central kernel over the model when its order is at most 150698880.
The target map consequently factors through the actual degree-6156 model.
An independent target lower bound makes this factor an isomorphism.

The finite-cover bound and both surjections remain explicit hypotheses:
this theorem does not supply an amalgam enumeration or source-generator map.
-/

public noncomputable section
namespace Sporadic.Janko3.SourceRecognition
open Theory.GroupTheory.SmallKernelPerfectFactorization

/-- A genuine cover of at most three times the model order supplies a
surjective model map commuting with the given target map. -/
theorem exists_model_factor_of_small_cover
    {E G : Type*} [Group E] [Group G] [Finite E]
    (f : E →* Model) (hf : Function.Surjective f)
    (q : E →* G) (hq : Function.Surjective q)
    (hcenter : Subgroup.center G = ⊥) (hbound : Nat.card E ≤ 150698880) :
    ∃ r : Model →* G, Function.Surjective r ∧ r.comp f = q := by
  apply exists_surjective_factor_of_card_le_three_mul f hf q hq hcenter
  simpa only [model_card,show 3 * 50232960 = 150698880 from rfl] using hbound

/-- With the independent lower bound, the same commuting factor is an
actual equivalence to the concrete J₃ model. -/
theorem exists_model_equiv_of_small_cover
    {E G : Type*} [Group E] [Group G] [Finite E] [Finite G]
    (f : E →* Model) (hf : Function.Surjective f)
    (q : E →* G) (hq : Function.Surjective q)
    (hcenter : Subgroup.center G = ⊥) (hbound : Nat.card E ≤ 150698880)
    (hlower : 50232960 ≤ Nat.card G) :
    ∃ e : Model ≃* G, e.toMonoidHom.comp f = q := by
  apply exists_equiv_of_card_le_three_mul f hf q hq hcenter
  · simpa only [model_card,show 3 * 50232960 = 150698880 from rfl] using hbound
  · simpa only [model_card] using hlower

end Sporadic.Janko3.SourceRecognition
