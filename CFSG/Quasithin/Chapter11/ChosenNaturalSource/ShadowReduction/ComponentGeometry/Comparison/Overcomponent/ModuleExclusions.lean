module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.ModuleExclusions.Models
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.ModuleExclusions.Actions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.ModuleExclusions.Orthogonal
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.Normalized

/-!
# The negative module branches of the proper-overcomponent comparison

Every larger quotient in the six quasisimple embedding pairs has neither
a full-normalizer FF chosen seed nor a marked doubled FF orbit, and it
cannot have the orthogonal-minus action. These comparisons apply to the
literal overcomponent and chosen module selected from the original flag.

The full-orbit FF conclusion additionally uses the earlier Source325Alternatives:
it treats invariant and doubled seeds separately. That premise is produced
by qt-baumann-fsu; the positive FF-or-orthogonal implication is produced by
qt-d-1222-normalized-nonff. Both remain explicit here and must be discharged
by qt-d-1222-shadow-component-comparison and its final parent
qt-d-1222-shadow-components. The A.3.12 shortlist and Hall/Cartan branch
also remain obligations of the comparison owner. This is not full 11.4.2.
Source: Aschbacher--Smith 11.4.2, p.776, using 3.2.5, 7.0.1 and B.4/B.5.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.ModuleExclusions
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {B J W : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T J W)

/-- None of the six larger quotient models admits an FF module on its
actual chosen seed, even through the full linear normalizer. -/
theorem seed_not_ff
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T J)
    (hp : QuasisimplePair B J) :
    ¬ IsFFModule (normalizerRepresentation D.chosenAction) := by
  let := h.quasisimple
  exact fun hff => not_restrictions_of_pair B J hp (seed_restrictions D h hff)

/-- A marked doubled orbit is excluded by B.5.1 on that orbit itself. -/
theorem doubled_not_ff
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T J)
    (hp : QuasisimplePair B J) (hd : D.MarkedDoubled) :
    ¬ IsFFModule D.sourceOrbitNormalizerRepresentation := by
  let := h.quasisimple
  exact fun hff => not_restrictions_of_pair B J hp (doubled_restrictions D h hd hff)

/-- The orthogonal-minus alternative is incompatible with every larger
quotient in the proper-overcomponent shortlist. -/
theorem not_orthogonal
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T J)
    (hp : QuasisimplePair B J) :
    ¬ Chapter7.NormalizedSource.OrthogonalMinusAlternative
      D.orbitRepresentation D.orbitComponent := by
  let := h.quasisimple
  exact fun ho => not_restrictions_of_pair B J hp (orthogonal_restrictions D h ho)

/-- The exact earlier 3.2.5 alternatives suffice to exclude FF on the full
orbit: invariant-seed and distinct doubled-seed cases are treated separately.
The earlier source alternatives are not asserted by this comparison. -/
theorem orbit_not_ff_of_source325
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T J)
    (hp : QuasisimplePair B J) (h325 : D.Source325Alternatives) :
    ¬ IsFFModule D.sourceOrbitNormalizerRepresentation := by
  intro hff
  rcases h325 with ⟨hW,_⟩ | ⟨hW,_,_⟩ | hd
  · have he : W = D.sourceOrbit := by rw [D.sourceOrbit_eq,hW]
    exact seed_not_ff D h hp ((D.chosen_normalizer_ff_iff_orbit_of_eq he).mpr hff)
  · have he : W = D.sourceOrbit := by rw [D.sourceOrbit_eq,hW]
    exact seed_not_ff D h hp ((D.chosen_normalizer_ff_iff_orbit_of_eq he).mpr hff)
  · exact doubled_not_ff D h hp hd hff

variable {L V : Subgroup G} {D₀ : Chapter12.Section02.ChosenModule T L V}

/-- Literal chosen-flag application. The proper-overcomponent geometry
constructs all hypotheses needed by the three negative module comparisons. -/
theorem ofFlag_negative_models
    (S : D₀.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D₀ S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J)
    (hp : QuasisimplePair (ofFlag S f X z H).Kz J)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) :
    (¬ IsFFModule (normalizerRepresentation D.chosenAction)) ∧
      (D.MarkedDoubled → ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) ∧
      ¬ Chapter7.NormalizedSource.OrthogonalMinusAlternative
        D.orbitRepresentation D.orbitComponent := by
  have hs := (source_hypotheses h hJ hlt hq).toHypothesis1221
  exact ⟨seed_not_ff D hs hp,doubled_not_ff D hs hp,not_orthogonal D hs hp⟩

/-- The actual source positive alternative contradicts the complete pair
list after earlier 3.2.5 is supplied. The positive normalized-nonFF theorem
and 3.2.5 remain inputs of final source assembly, not conclusions here. -/
theorem ofFlag_false_of_source325_and_alternative
    (S : D₀.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D₀ S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J)
    (hp : QuasisimplePair (ofFlag S f X z H).Kz J)
    (hq : IsQuasisimple (J ⧸ pCore 2 J))
    (h325 : D.Source325Alternatives)
    (halt : IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      Chapter7.NormalizedSource.OrthogonalMinusAlternative
        D.orbitRepresentation D.orbitComponent) : False := by
  have hs := (source_hypotheses h hJ hlt hq).toHypothesis1221
  exact halt.elim (orbit_not_ff_of_source325 D hs hp h325) (not_orthogonal D hs hp)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.ModuleExclusions
