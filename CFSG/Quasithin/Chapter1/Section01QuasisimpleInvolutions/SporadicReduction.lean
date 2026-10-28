module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Sporadic
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.JankoOne
public import Theory.SpecificGroups.Held.LocalPairs.SylowPointwise
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Rudvalis
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer

/-!
# The remaining source sporadic action inputs

All Theorem C sporadic models are inspected. Eight allowed models yield the
canonical row (f), and the actual J₁ centralizer excludes that model. The
only remaining alternatives are genuine Held and Rudvalis quotient models.
Their adapters take precisely full Held permutation realization and preservation
of the Ru point-stabilizer class. The Ru normalizer computation is discharged.

The missing producers are `qt-held-outer-realization` and
`qt-1-03-outer-rudvalis-stabilizer`; the final classifier must supply both
when their respective model occurs. These conditional adapters do not claim
the unconditional source sporadic classification.
Source: Aschbacher--Smith, proof of 1.1.5(3)(f), printed p.503.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels
open ChapterA.Section02
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
  {α : MulAut L} {P : Sylow 2 L}

/-- The precise missing Held producer is full permutation realization. -/
theorem MarkedInvolution.modelAction_he_of_realization (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* Held.He)
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom) :
    ModelAction115 L α := by
  apply d.sporadic_of_quotient_inner .he (by intro h; cases h) e
  obtain ⟨_, _, Q, hQ⟩ := d.centralQuotient_model_inputs e
  exact Held.LocalPairs.SylowPointwise.isInner_of_fixes_sylow hrealize Q _ hQ

/-- The precise missing Ru producer is preservation of its point-stabilizer
class. Its permutation-normalizer computation is already discharged. -/
theorem MarkedInvolution.modelAction_ru_of_stabilizers (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* Rudvalis.Model)
    (hstable : ∀ f : MulAut Rudvalis.Model, ∃ y : Fin 4060,
      (MulAction.stabilizer Rudvalis.Model (0 : Fin 4060)).map f.toMonoidHom =
        MulAction.stabilizer Rudvalis.Model y) : ModelAction115 L α := by
  exact d.sporadic_of_quotient_inner .ru (by intro h; cases h) e
    (XiEmbedding.OuterModels.rudvalis_conj_surjective_of_action hstable
      Rudvalis.outer_permutation_normalizer_eq _)

/-- All Theorem C sporadic alternatives reduce to the canonical conclusion
or the two genuine outstanding model-action calculations. -/
theorem MarkedInvolution.sporadic_reduction (d : MarkedInvolution α P)
    (hmodel : IsTheoremCSporadicModel (L ⧸ center L)) :
    ModelAction115 L α ∨ Nonempty (L ⧸ center L ≃* Held.He) ∨
      Nonempty (L ⧸ center L ≃* Rudvalis.Model) := by
  rcases hmodel with ⟨name, hn, ⟨e⟩⟩ | ⟨e⟩
  · cases name with
    | m11 => exact Or.inl (d.modelAction_m11 e)
    | m12 => exact Or.inl (d.modelAction_m12 e)
    | m22 => exact Or.inl (d.modelAction_m22 e)
    | m23 => exact Or.inl (d.modelAction_m23 e)
    | m24 => exact Or.inl (d.modelAction_m24 e)
    | j2 => exact Or.inl (d.modelAction_j2 e)
    | j3 => exact (hn rfl).elim
    | j4 => exact Or.inl (d.modelAction_j4 e)
    | hs => exact Or.inl (d.modelAction_hs e)
    | he => exact Or.inr (Or.inl ⟨e⟩)
    | ru => exact Or.inr (Or.inr ⟨e⟩)
  · obtain ⟨e⟩ := e
    exact (d.not_janko_one e).elim

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
