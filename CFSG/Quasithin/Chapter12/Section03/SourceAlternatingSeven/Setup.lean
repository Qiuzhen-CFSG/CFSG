module

public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.Representation.BinarySevenCode.Normalizer

/-!
# The literal A₇ case of 12.3.1

The quotient is by the preimage of the centre of L/O₂(L) under the original
projection. In particular a triple cover has not been replaced by A₇.
`Setup` retains the original chosen Irr⁺ member. `LocalAnalysis` is the
explicit output required from 12.3.3--8: natural coordinates, their actual
normalizer action, fusion control, and the two point-centralizer bounds.
These conclusions are not included in the source hypotheses.

The remaining source proof must construct this local analysis, establish
weak closure including the simplex case, and perform the final component
argument. Source: Aschbacher--Smith, 12.3.1--13, printed pp.807--812.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal quotient L/O₂,Z(L), before any conclusion about its centre. -/
abbrev CentralQuotient (L : Subgroup G) :=
  L ⧸ (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L))

/-- The ambient escape consequence of 12.2.13, uniformly for every maximal
faithful member and every original chosen module. Uniformity permits the
source proof to apply its local analysis to a second maximal component.
The Chapter 13 adapter derives this from its actual ambient exclusions. -/
def CentralizerEscape (T : Sylow 2 G) : Prop :=
  ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
    ChosenModule T L V →
    ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G)

/-- A proposed A₇ row and the original choice V, with only source inputs. -/
structure Setup (T : Sylow 2 G) (L V : Subgroup G) where
  hypothesis : Hypothesis1223 KnownSimple.IsKnownSimple T L
  chosen : ChosenModule T L V
  quotient : CentralQuotient L ≃* alternatingGroup (Fin 7)

namespace Setup
variable {T : Sylow 2 G} {L V : Subgroup G} (S : Setup T L V)

/-- The original L-to-A₇ projection; its kernel includes the central cover. -/
def projection : L →* alternatingGroup (Fin 7) :=
  S.quotient.toMonoidHom.comp (QuotientGroup.mk' _)

/-- The source projection is onto the actual alternating group. -/
theorem projection_surjective : Function.Surjective S.projection :=
  S.quotient.surjective.comp (QuotientGroup.mk'_surjective _)

/-- A literal natural-module marking and the ambient conclusions of
12.3.3--8. Construction of this record is a separate source obligation. -/
structure LocalAnalysis where
  model : NormalizerModel V
  component_action : ∀ l : L,
    model.permutation ⟨l, S.chosen.normalizes l.property⟩ = (S.projection l).val
  controlsFusion : ∀ x y : G, x ∈ V → y ∈ V → x ≠ 1 → y ≠ 1 →
    (∃ g : G, g * x * g⁻¹ = y) → ∃ l ∈ L, l * x * l⁻¹ = y
  pointCentralizers : ∀ v : V, v ≠ 1 →
    (weight (model.coordinates v).toAdd.val = 2 ∨
      weight (model.coordinates v).toAdd.val = 6) →
    centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G)

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
