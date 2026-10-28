module

public import Stellmacher.Recognition.NormalEightExoticExtension256Setup
public import Theory.SpecificGroups.ExoticTwoGroup.ActionModel

/-!
# Coordinate conjugation for the order-256 action problem

Conjugation transported to the coordinate C₄-square has kernel the abelian
base and image of order sixteen. This common interface supports the independent
inner-action normalization and outer swap-existence proofs, and their final
assembly in `NormalEightExoticExtension256Action`.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.4(c), printed p.386.
-/

open Subgroup C4SquareExtension

namespace Stellmacher.Recognition.NormalEightExoticExtension256

/-- Conjugation on the base, expressed in the chosen C₄-square coordinates. -/
public abbrev modelAction {P : Type*} [Group P] (D : Subgroup P) [D.Normal]
    (e : D ≃* Model) : P →* MulAut Model :=
  (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : P →* MulAut D)

/-- The transported action is still faithful modulo the abelian base. -/
public theorem modelAction_ker {P : Type*} [Group P] (D : Subgroup P)
    [D.Normal] [IsMulCommutative D] (hDC : centralizer (D : Set P) ≤ D)
    (e : D ≃* Model) : (modelAction D e).ker = D := by
  rw [modelAction, MonoidHom.ker_comp_of_injective _ _ (MulAut.congr e).injective]
  exact conjNormal_ker_eq_of_selfCentralizing_abelian D hDC

/-- Transporting the conjugation image preserves its order sixteen. -/
public theorem card_modelAction_range {P : Type*} [Group P] [Finite P]
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D) (e : D ≃* Model)
    (hcard : Nat.card P = 256) : Nat.card (modelAction D e).range = 16 := by
  rw [MonoidHom.range_comp, card_map_of_injective (MulAut.congr e).injective]
  exact card_conjugation_range D hDC ⟨e⟩ hcard

end Stellmacher.Recognition.NormalEightExoticExtension256
