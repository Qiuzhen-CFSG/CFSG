module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.Source
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.StandardModule

/-!
# The two independent inputs for the bounded Rudvalis exclusion

Small-module recognition identifies the actual action of an arbitrary finite
quasisimple central cover, including its group and linear markings. It has no
cubic-ratio premise. The second calculation concerns the full linear normalizer
of the fixed degree-28 action; it therefore includes every ambient extension.
These are obligations, not proved classification results.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
Ru paragraph, and Theorem 6.6; Aschbacher--Smith K.4, printed p.457.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion
open Theory.GroupTheory Subgroup Representation.BinaryOffender
open scoped ENNReal
universe u v

/-- Comparison of the concrete matrix and permutation groups, with both
standard generators marked. This is not inferred from a family name or order. -/
def StandardComparison : Prop :=
  ∃ e : Rudvalis.Model ≃* standardGroup,
    (e Rudvalis.a).val = generatorA ∧ (e Rudvalis.b).val = generatorB

/-- Recognition of the entire marked module, including all possible covers.
The output is an actual group equivalence and an intertwining linear equivalence. -/
def SmallModuleRecognition : Prop :=
  ∀ {L : Type u} {V : Type v} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) L V), Function.Injective σ → σ.IsIrreducible →
    Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.ru.Carrier) →
    Module.finrank (ZMod 2) V ≤ 36 →
    ∃ (e : L ≃* standardGroup) (E : V ≃ₗ[ZMod 2] Space),
      ∀ l v, E (σ l v) = standardRepresentation (e l) (E v)

/-- A fixed finite action calculation, independent of source-module recognition. -/
def StandardNormalizerExclusion : Prop :=
  2 < cubicRatio (normalizerRepresentation standardRepresentation)

/-- The source application supplies these structural hypotheses through its
marking, so the finite calculation need not independently certify them. -/
def SourceNormalizerExclusion : Prop :=
  IsQuasisimple standardGroup → standardRepresentation.IsIrreducible →
    StandardNormalizerExclusion

end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion
