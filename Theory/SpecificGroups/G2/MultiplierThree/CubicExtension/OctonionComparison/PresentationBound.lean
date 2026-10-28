module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.Alphabet
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalPresentation
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations

/-!
# Subgroup reduction of the six-relator G₂(3) presentation bound

The checked 364-coset cover by the fixed max3 subgroup, together with its finite
order bound 11664, gives the finite order bound 4245696 for the unchanged
six-relator presentation. The subgroup bound follows from the checked local
presentation bound and the seven proved identities on the literal max3 words.
Thus `finite_card_presented_le` has no remaining certificate hypotheses.

The proof uses the surjection from subgroup elements paired with coset
representatives. It does not infer finiteness from a numerical `Nat.card`
inequality, or from the order of a permutation quotient.

Source: the ATLAS words retained in `Presentation` and `PresentationBound/source`.
-/

namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound

/-- Conditional assembly; both certificates must be supplied for the final bound. -/
public theorem finite_card_presented_le_of_subgroup
    (hlocal : Finite boundSubgroup ∧ Nat.card boundSubgroup ≤ 11664)
    (cover : Subgroup.GeneratorCosetCover boundSubgroup Presentation.generator (Fin 364)) :
    Finite Presentation.Presented ∧ Nat.card Presentation.Presented ≤ 4245696 := by
  let := hlocal.1
  have hgen : Subgroup.closure (Set.range Presentation.generator) = ⊤ :=
    PresentedGroup.closure_range_of (Set.range Presentation.relator)
  obtain ⟨hfinite, hcard⟩ := cover.finite_card_le hgen
  refine ⟨hfinite, hcard.trans ?_⟩
  simpa using Nat.mul_le_mul_right 364 hlocal.2

/-- The marked local relation certificate, its independent order proof, and the
ambient cover discharge exactly the premises of the presentation bound. -/
public theorem finite_card_presented_le_of_local
    (hrel : ∀ i, Subgroup.CosetWordCertificate.eval boundGenerator (localRelatorLetters i) = 1)
    (hlocal : Finite LocalPresented ∧ Nat.card LocalPresented ≤ 11664)
    (cover : Subgroup.GeneratorCosetCover boundSubgroup Presentation.generator (Fin 364)) :
    Finite Presentation.Presented ∧ Nat.card Presentation.Presented ≤ 4245696 :=
  finite_card_presented_le_of_subgroup (finite_card_boundSubgroup_le_of_local hrel hlocal) cover

/-- The literal six-relator ATLAS presentation is finite of order at most 4,245,696.
The lifted local relations, local finite bound, and ambient coset cover discharge
all three independent premises of the assembly theorem. -/
public theorem finite_card_presented_le :
    Finite Presentation.Presented ∧ Nat.card Presentation.Presented ≤ 4245696 :=
  finite_card_presented_le_of_local local_relations finite_card_localPresented_le boundCosetCover

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound
