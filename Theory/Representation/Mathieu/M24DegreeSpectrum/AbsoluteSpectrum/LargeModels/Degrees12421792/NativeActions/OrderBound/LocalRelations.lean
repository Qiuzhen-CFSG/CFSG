module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalRelations.Contracts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalOrder

/-!
# Assembly of the actual max8 local identities

The first two identities follow from the original source relators. The quartic
identity and the six mixed identities remain explicit, independent obligations.
Combining their eventual proofs gives all nine literal local relations and the
finite bound on the actual subgroup. This module does not yet assert either
unconditional conclusion. See `LocalRelations/source/README.md`.

Source: John Bray's ATLAS M24G1-P1 and the M24G1-max8W1 subgroup program.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound
open Subgroup.CosetWordCertificate

/-- Conditional assembly; both remaining source branches still require proofs. -/
theorem local_relations_of_remaining (hq : LocalRelations.QuarticRelation)
    (hm : LocalRelations.MixedRelations) :
    ∀ i : Fin 9, eval boundGenerator (localRelatorLetters i) = 1 := by
  intro i
  fin_cases i
  · exact localRelator_zero_holds
  · exact localRelator_one_holds
  · exact hq
  · exact hm 0
  · exact hm 1
  · exact hm 2
  · exact hm 3
  · exact hm 4
  · exact hm 5

/-- Actual subgroup consumer, with the unproved source branches left explicit. -/
theorem boundSubgroup_finite_card_le_of_remaining
    (hq : LocalRelations.QuarticRelation) (hm : LocalRelations.MixedRelations) :
    Finite boundSubgroup ∧ Nat.card boundSubgroup ≤ 6072 :=
  boundSubgroup_finite_card_le (local_relations_of_remaining hq hm)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound
