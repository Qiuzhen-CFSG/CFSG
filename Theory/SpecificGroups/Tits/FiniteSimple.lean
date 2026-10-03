module

public import Theory.SpecificGroups.Tits.PresentationUpperBound
public import Theory.SpecificGroups.Tits.FiniteImageSimple

/-!
# Finiteness, order, and simplicity of Parrott's presented group

The certified coset cover proves that the actual ten-generator, 37-relator
presentation is finite of order at most 17971200. Its certified surjection onto
the Atlas permutation group of order 17971200 is therefore bijective. This
identifies the presented group faithfully with the concrete simple group,
proving its exact order and simplicity. The finiteness instance is re-exported
from `PresentationUpperBound`.

Source: Parrott, “A Characterization of the Tits' Simple Group” (1972), §5,
p. 683, transcribed in `refs/original/n-group-global/parrott-tits-presentation.md`;
the concrete image uses `refs/original/n-group-global/atlas-tits-p1600-{a,b}.g`.
-/

namespace Tits

/-- The finite upper bound and matching image order force faithfulness. -/
public theorem parrottFiniteImageMap_bijective :
    Function.Bijective parrottFiniteImageMap := by
  apply parrottFiniteImageMap_surjective.bijective_of_nat_card_le
  rw [atlas1600Group_card]
  exact parrottGroup_card_le

/-- The certified permutation representation of the presentation is faithful. -/
public theorem parrottFiniteImageMap_injective :
    Function.Injective parrottFiniteImageMap :=
  parrottFiniteImageMap_bijective.1

/-- The actual presented group is isomorphic to its certified finite image. -/
public noncomputable def parrottFiniteImageEquiv : ParrottGroup ≃* Atlas1600Group :=
  MulEquiv.ofBijective parrottFiniteImageMap parrottFiniteImageMap_bijective

/-- The faithful identification agrees with the original presentation map. -/
@[simp] public theorem parrottFiniteImageEquiv_apply (x : ParrottGroup) :
    parrottFiniteImageEquiv x = parrottFiniteImageMap x := by rfl

/-- Each of the ten generators has its certified Atlas image under the isomorphism. -/
@[simp] public theorem parrottFiniteImageEquiv_generator (i : ParrottGenerator) :
    parrottFiniteImageEquiv (parrottGenerator i) = atlas1600ParrottAssignment i :=
  parrottFiniteImageMap_generator i

/-- The exact order of Parrott's presented group. -/
public theorem parrottGroup_card : Nat.card ParrottGroup = 17971200 :=
  (Nat.card_congr parrottFiniteImageEquiv.toEquiv).trans atlas1600Group_card

/-- Simplicity transfers along the faithful identification with the finite image. -/
public instance parrottGroup_isSimpleGroup : IsSimpleGroup ParrottGroup :=
  parrottFiniteImageEquiv.isSimpleGroup

end Tits
