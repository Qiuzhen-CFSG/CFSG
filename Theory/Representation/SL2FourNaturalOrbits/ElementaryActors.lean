module

public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.FiveLines
public import Theory.SpecificGroups.Alternating.FiveElementaryActors

/-!
# Elementary automizers of the marked natural SL₂(4)

The natural action on the five F₄-lines identifies the literal determinant-one
matrix group with A₅. Transporting the proved A₅ automorphism identification
gives Aut(SL₂(4)) ≃ S₅, and hence elementary two-subgroups have order at most
four. The final theorem applies this bound to the actual conjugation action
of an elementary subgroup on a specified normal copy of SL₂(4); disjointness
from its literal centralizer is the entire faithfulness input.

This is the marked automizer step used for the natural SL₂(4) branch of
Aschbacher–Smith 13.7.13 and 13.7.16(1), printed pp.942–944. The five-line
identification retains the original natural action from Section 6.2.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace Representation.SL2FourNatural
open SemilinearNormalizer

/-- The five-line action identifies the actual natural SL₂(4) with A₅. -/
noncomputable def alternatingFiveEquiv : SL ≃* alternatingGroup (Fin 5) :=
  (MonoidHom.ofInjective specialFiveLines_injective).trans
    (MulEquiv.subgroupCongr specialFiveLines_range)

/-- The identification preserves the specified five-line permutation action. -/
theorem alternatingFiveEquiv_apply (g : SL) :
    (alternatingFiveEquiv g : Equiv.Perm (Fin 5)) = specialFiveLines g := rfl

/-- The full automorphism group of the concrete SL₂(4) is S₅. -/
noncomputable def automorphismSymmetricFiveEquiv : MulAut SL ≃* Equiv.Perm (Fin 5) :=
  (MulAut.congr alternatingFiveEquiv).trans
    Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv.symm

/-- The automorphism group of the marked SL₂(4) has elementary two-rank at most two. -/
theorem automorphism_primeRank_two_le : primeRank 2 (MulAut SL) ≤ 2 := by
  rw [primeRank_equiv 2 (MulAut.congr alternatingFiveEquiv)]
  exact Theory.SpecificGroups.Alternating.FiveExtensionAction.automorphism_primeRank_two_le

/-- Every elementary two-subgroup of the exact automorphism group has order at most four. -/
theorem elementary_automorphism_card_le_four (E : Subgroup (MulAut SL))
    [IsElementaryAbelian 2 E] : Nat.card E ≤ 4 :=
  (primeRank_le_iff_elementary_card_le _).mp automorphism_primeRank_two_le E inferInstance

/-- An actual elementary actor disjoint from the selected normal SL₂(4) centralizer has order at most four. -/
theorem elementary_card_le_four_of_disjoint {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) [K.Normal] (eK : K ≃* SL)
    (E : Subgroup H) [IsElementaryAbelian 2 E]
    (hd : Disjoint E (centralizer (K : Set H))) : Nat.card E ≤ 4 :=
  Theory.SpecificGroups.Alternating.FiveExtensionAction.elementary_card_le_four_of_disjoint
    K (eK.trans alternatingFiveEquiv) E hd

end Representation.SL2FourNatural
