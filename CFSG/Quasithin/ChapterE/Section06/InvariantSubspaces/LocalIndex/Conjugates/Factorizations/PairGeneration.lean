module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.Inputs
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration.LinearQuotient
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration.AlternatingThree
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration.Alternating
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction

/-!
# Conditional assembly of the C.5.6 generating pair

Two concrete calculations give the pair: conjugate Sylow/root groups in
SL₂, and commuting-transposition four-groups in S₅. The transport retains
the actual two-core and lifts the conjugator into L. The supplied span
S = UˣQ replaces both copies of S by the corresponding copies of Uˣ.

The A₃ branch is proved directly using the three-coset action. The even-field
quotient is constructed from the published internal natural coordinates,
and the actual A₅ action is supplied by its proved construction. Only the
linear coordinates and actual A₅ Thompson image remain source inputs to
`pairGenerationInput_of_coordinates_and_thompson`. The earlier alternative
assembly through a general rank-one quotient witness is retained separately.
The parent factorization module independently removes Q by two-perfection.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.6,
printed pp.156–157 (PDF pp.167–168), following C.5.4 on p.155.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations
open Subgroup PairGeneration
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Assemble all three block types once their actual quotient/action
identifications have been constructed. No factorization beyond the
contract's supplied Baumann span is used. -/
theorem pairGenerationInput_of_models (K : GroupClass.{u})
    (hn : RankOneQuotientInput (G := G) K)
    (ha : Baumann.AlternatingFive.NaturalActionInput (G := G) K)
    (hj : Baumann.AlternatingFive.ThompsonImageInput (G := G) K) :
    PairGenerationInput (G := G) K := by
  intro A H R L h hb x hx hnc hspan
  rcases h.block with hL | hL | hL
  · exact rankOne_pair_of_input hn h hb (Or.inl hL) hx hnc hspan
  · exact rankOne_pair_of_input hn h hb (Or.inr hL) hx hnc hspan
  · exact alternating_pair_of_inputs ha hj h hL hspan

/-- The actual alternating-five action is already constructed. Only the
rank-one quotient and the actual Thompson-image calculation remain to be
discharged before this yields the source generating-pair input. -/
theorem pairGenerationInput_of_quotient_and_thompson (K : GroupClass.{u})
    (hn : RankOneQuotientInput (G := G) K)
    (hj : Baumann.AlternatingFive.ThompsonImageInput (G := G) K) :
    PairGenerationInput (G := G) K :=
  pairGenerationInput_of_models K hn Baumann.AlternatingFive.naturalActionInput hj

/-- The A₃ branch and the quotient transports are proved here. The two
remaining source inputs have separate owners: the internal natural Baumann
coordinates and the actual A₅ Thompson image. -/
theorem pairGenerationInput_of_coordinates_and_thompson (K : GroupClass.{u})
    (hl : NaturalIndices.LinearCoordinatesInput (G := G) K)
    (hj : Baumann.AlternatingFive.ThompsonImageInput (G := G) K) :
    PairGenerationInput (G := G) K := by
  intro A H R L h hb x hx hnc hspan
  rcases h.block with ⟨n, hn⟩ | ha3 | ha5
  · exact linear_pair_of_input hl h hb hn hspan
  · exact alternatingThree_pair h hb ha3 hnc hspan
  · exact alternating_pair_of_inputs Baumann.AlternatingFive.naturalActionInput hj h ha5 hspan

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations

end
