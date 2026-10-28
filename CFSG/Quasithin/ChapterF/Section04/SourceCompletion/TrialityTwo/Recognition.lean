module
public import Theory.SpecificGroups.Triality.BinaryTwistRelations
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.BinaryTwist

/-!
# Recognition of small binary triality completions

The short-root rank-one identity excludes the remaining highest-root twist.
The zero orbit already has the native sixth-power relation, so comparison of
the faithful coset geometries supplies an isomorphism preserving both entire
endpoint maps. No ambient simplicity or classification hypothesis is needed.

This gives the triality-at-two case of Aschbacher--Smith F.4.17,24, printed
pp.282--283,287 (`refs/quasithin.pdf`), by explicit root identities in place of
the general Moufang-polygon classification used in the source.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
variable {G : Type*} [Group G] [Finite G] (c : Completion G)

/-- A faithful completion with at most the native order is the native group,
with both endpoint embeddings preserved element by element. -/
theorem exists_mulEquiv_of_order_bound (horder : Nat.card G≤Nat.card Model) :
    ∃ f : G ≃* Model, (∀ x, f (c.left x)=modelCompletion.left x) ∧
      (∀ x, f (c.right x)=modelCompletion.right x) := by
  rcases c.recognition_or_twisted_relation horder with hf | ⟨_,_,_,_,hpow,_⟩
  · exact hf
  · exact (_root_.Triality.Standard.BinaryTwistRelations.twisted_product_six_ne_one
      c.left c.right c.right_injective c.compatible hpow).elim

end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
