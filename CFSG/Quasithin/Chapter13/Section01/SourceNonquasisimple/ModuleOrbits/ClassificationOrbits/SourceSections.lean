module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.ClassificationOrbits.NaturalRows
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.ClassificationOrbits.RankFour

/-!
# Quasisimple source sections in the literal centralizer analysis

The two-copy branch constructs its LT marking from the source coordinates.
For an irreducible source section, the small-action theorem gives a natural
SL₂(4) quotient, a natural SL₃(2) quotient, or the deleted S₅ action. The
linear-three quotient is retained through its zero-kernel or rank-four
cover application, so both original centralizer interfaces are discharged.
This closes every quasisimple-source branch except the deleted S₅ Sylow
clause, whose actual marking is retained explicitly.

The full source assembly, including the product and hyperplane transports
and deleted S₅ Sylow clause, remains with qt-d-1317-module-orbits. The earlier
Thompson movement is discharged by qt-d-1317-source and its supplement input.
Source: Aschbacher--Smith 13.1.10--12, pp.871--874; B.5.1 and B.5.6.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 SourceCentralizerStructure.Elimination
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- Both possible central kernels in an original natural three-space section
feed the centralizer consumers through their genuine action markings. -/
theorem centralizer_inputs_of_three_section
    [IsElementaryAbelian 2 (normalizerMoved L)] (h : Context T L p)
    {H : Subgroup (NormalizerReducedAction.Star L)}
    (hCH : NormalizerReducedAction.componentImage L ≤ H)
    (s : MovedSection ((reducedRepresentation L).comp H.subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf H))
    (hi : IsIrrPlus ((reducedRepresentation L).comp H.subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf H) s.space.toSubmodule)
    (a : ActionEquiv (s.action.comp
      ((NormalizerReducedAction.componentImage L).subgroupOf H).subtype)
      (linearNatural BinaryField.two 3)) : OrbitFacts T L p ∧ SieveActions h := by
  by_cases hz : s.central.toSubmodule = ⊥
  · let c := componentSectionEquiv h.hypothesis h.many h.maximal h.nonquasisimple hCH s
    let d := naturalOrbitMarking (composeAction c (composeAction (sectionQuotientEquiv s hz) a))
    exact ⟨d.orbitFacts h,d.sieveActions h⟩
  · exact centralizer_inputs_of_central_three_section h hCH s hi hz a

/-- The genuine irreducible B.5 branch now leaves only the deleted S5 row.
The natural quotient of the rank-four row is retained until its orbit and
sieve application, rather than discarded into the dimension-only record. -/
theorem irreducibleReduced_inputs_or_symmetric (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (hi : IrreducibleReducedCase L) :
    (OrbitFacts T L p ∧ SieveActions h) ∨ Nonempty (SymmetricFiveRow T L) := by
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.hypothesis.simpleQTKE h.maximal h.sylow_normalizes).1
  obtain ⟨d,hd,hsmall⟩ := irreducibleReduced_small h.hypothesis h.many h.maximal
    h.nonquasisimple hmove hi
  have hj := componentImage_le_reducedOffender h.hypothesis h.maximal h.nonquasisimple hmove
  rcases hsmall with ⟨F,hF,⟨a⟩⟩ | ha | ha
  · exact Or.inl ((irreducibleFourMarking h.hypothesis h.many h.maximal h.nonquasisimple
      hmove d.sectionData F hF a).centralizer_inputs h)
  · obtain ⟨a⟩ := ha
    exact Or.inl (centralizer_inputs_of_three_section h hj d.sectionData
      ((irreducibleSectionCase_iff _).mp hd).1 a)
  · obtain ⟨a⟩ := ha
    exact Or.inr ⟨irreducibleSymmetricFiveMarking h.hypothesis h.many h.maximal
      h.nonquasisimple hmove d.sectionData ((irreducibleSectionCase_iff _).mp hd).1 a⟩

/-- All quasisimple source sections give the literal centralizer inputs,
except for the retained deleted-S5 Sylow-action branch. -/
theorem quasisimple_inputs_or_symmetric (h : Context T L p)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (d : ProjectiveLine.QuasisimpleSourceConclusion
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L)))) :
    (OrbitFacts T L p ∧ SieveActions h) ∨ Nonempty (SymmetricFiveRow T L) := by
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.hypothesis.simpleQTKE h.maximal h.sylow_normalizes).1
  rcases quasisimple_marked_or_irreducible h.hypothesis h.many h.maximal
      h.nonquasisimple hmove d with hm | hi
  · obtain ⟨m⟩ := hm
    exact Or.inl (m.centralizer_inputs h)
  · exact irreducibleReduced_inputs_or_symmetric h hmove hi

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
