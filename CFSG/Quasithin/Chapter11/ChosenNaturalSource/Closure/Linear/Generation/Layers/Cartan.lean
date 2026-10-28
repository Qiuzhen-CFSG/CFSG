module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Layers.Models
public import Theory.Representation.SpecialLinearThreeCartanFixed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus

/-!
# The actual Cartan has zero fixed space on both layers

The original component map embeds the odd Cartan into SL₃(q), since its kernel
is a two-group. The original Hall-Cartan calculation gives order (q−1)².
The natural and contragredient order arguments therefore annihilate every
fixed coordinate, and the literal quotient-action equations transport this
back to the two binary sections. No alignment with a selected diagonal torus
or additional model hypothesis is required.

Source: Aschbacher–Smith, 11.5.7, printed pp.781–782; G.2.5, pp.335–336.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
open Subgroup Representation Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open ChapterG.Section02.LinearThree
open Recognition Recognition.Hypothesis
attribute [local instance] ZMod.algebra

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
  (hUT : E.W ≤ (T : Subgroup G))
  (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)

private def layerCartanMap (hX : LocalGeometry.IsCartan T L E.X) :
    E.X →* SL(3,E.input.field.Carrier) :=
  (Block.Special.componentModel E d).comp (inclusion (hX.1.trans inf_le_left))

private theorem layerCartanMap_injective (hX : LocalGeometry.IsCartan T L E.X) :
    Function.Injective (layerCartanMap E d hX) := by
  apply SpecialLinearThreeCartanFixed.injective_of_odd_two_kernel _ hX.odd
  have he : (layerCartanMap E d hX).ker =
      (pCore 2 L).comap (inclusion (hX.1.trans inf_le_left)) := by
    ext z
    change d.model (starProjection (setup E) (inclusion (hX.1.trans inf_le_left) z)) = 1 ↔ _
    rw [map_eq_one_iff _ d.model.injective]
    change inclusion (hX.1.trans inf_le_left) z ∈ (starProjection (setup E)).ker ↔ _
    rw [Block.starProjection_ker E]
    rfl
  rw [he]
  exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)

private theorem layerField_large : 2 < Nat.card E.input.field.Carrier := by
  have h : 4 ≤ Nat.card E.input.field.Carrier := by
    rw [E.input.field.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) E.input.nonbinary
  omega

private theorem layerField_predecessor_odd : Odd (Nat.card E.input.field.Carrier - 1) := by
  rw [E.input.field.card_eq]
  exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by decide))
    (even_two.pow_of_ne_zero (Nat.ne_of_gt E.input.field.degree_pos)) odd_one

private theorem layerCartan_card (hX : LocalGeometry.IsCartan T L E.X) :
    Nat.card E.X = (Nat.card E.input.field.Carrier - 1)^2 := by
  rw [(LocalGeometry.coordinates D E.input).cartan_card hX, E.input.field.card_eq]

variable [((thirdLayer E x y).subgroupOf (threeCore E x y)).Normal]
  [((triple E x y).subgroupOf (thirdLayer E x y)).Normal]
  [IsElementaryAbelian 2 (threeCore E x y ⧸
    (thirdLayer E x y).subgroupOf (threeCore E x y))]
  [IsElementaryAbelian 2 (thirdLayer E x y ⧸
    (triple E x y).subgroupOf (thirdLayer E x y))]

local instance cartanUpperNormal :
    ((S₃ (setup E) x y).subgroupOf (S (setup E) x y)).Normal :=
  inferInstanceAs (((thirdLayer E x y).subgroupOf (threeCore E x y)).Normal)
local instance cartanLowerNormal :
    ((S₂ (setup E) x y).subgroupOf (S₃ (setup E) x y)).Normal :=
  inferInstanceAs (((triple E x y).subgroupOf (thirdLayer E x y)).Normal)
local instance cartanUpperElementary : IsElementaryAbelian 2 (UpperQuotient (setup E) x y) :=
  inferInstanceAs (IsElementaryAbelian 2 (threeCore E x y ⧸
    (thirdLayer E x y).subgroupOf (threeCore E x y)))
local instance cartanLowerElementary : IsElementaryAbelian 2 (LowerQuotient (setup E) x y) :=
  inferInstanceAs (IsElementaryAbelian 2 (thirdLayer E x y ⧸
    (triple E x y).subgroupOf (thirdLayer E x y)))

namespace UpperActions
variable {E} (a : UpperActions E x y) {r s : ℕ}

/-- Cartan equivariance on the literal upper quotient. -/
theorem upper_cartan_equivariant
    (m : NaturalGeometry.Model d (d.sourceStarComparison hUT hf) r)
    (hX : LocalGeometry.IsCartan T L E.X) (z : E.X) (v) (i : Fin r) :
    m.equivalence (a.upperAction (inclusion (Cartan_le_threeGroup E d hUT hf hX) z) v) i =
      (Block.Special.componentModel E d (inclusion (hX.1.trans inf_le_left) z)).val *ᵥ
        (m.equivalence v i) := by
  rw [a.upperAction_eq_model d hUT hf m]
  change m.equivalence (m.representation ((d.sourceStarComparison hUT hf).projection
    (inclusion (d.L_le_I hUT hf) (inclusion (hX.1.trans inf_le_left) z))) v) i = _
  rw [(d.sourceStarComparison hUT hf).projection_on_L]
  exact m.equivariant _ v i

/-- Cartan equivariance on the literal lower quotient. -/
theorem lower_cartan_equivariant
    (m : DualGeometry.MarkedModel.Model d (d.sourceStarComparison hUT hf) s)
    (hX : LocalGeometry.IsCartan T L E.X) (z : E.X) (v) (i : Fin s) :
    m.equivalence (a.lowerAction (inclusion (Cartan_le_threeGroup E d hUT hf hX) z) v) i =
      FrameGeometry.natural.dual
        (Block.Special.componentModel E d (inclusion (hX.1.trans inf_le_left) z))
        (m.equivalence v i) := by
  rw [a.lowerAction_eq_model d hUT hf m]
  change m.equivalence (m.representation ((d.sourceStarComparison hUT hf).projection
    (inclusion (d.L_le_I hUT hf) (inclusion (hX.1.trans inf_le_left) z))) v) i = _
  rw [(d.sourceStarComparison hUT hf).projection_on_L]
  exact (m.equivariant _ v i).trans (DualGeometry.ModelGeometry.dualAction_model d _ _)

/-- The original Cartan fixes only zero in the upper binary layer. -/
theorem upper_cartan_fixed_eq_zero
    (m : NaturalGeometry.Model d (d.sourceStarComparison hUT hf) r)
    (hX : LocalGeometry.IsCartan T L E.X) (v)
    (hv : ∀ z : E.X, a.upperAction
      (inclusion (Cartan_le_threeGroup E d hUT hf hX) z) v = v) : v = 0 := by
  apply m.equivalence.injective
  rw [map_zero]
  funext i
  apply SpecialLinearThreeCartanFixed.natural_fixed_eq_zero
    (layerField_large E) (layerField_predecessor_odd E) (layerCartan_card E hX)
    (layerCartanMap E d hX) (layerCartanMap_injective E d hX)
  intro z
  exact (a.upper_cartan_equivariant d hUT hf m hX z v i).symm.trans
    (congrArg (fun w => m.equivalence w i) (hv z))

/-- The original Cartan fixes only zero in the lower binary layer. -/
theorem lower_cartan_fixed_eq_zero
    (m : DualGeometry.MarkedModel.Model d (d.sourceStarComparison hUT hf) s)
    (hX : LocalGeometry.IsCartan T L E.X) (v)
    (hv : ∀ z : E.X, a.lowerAction
      (inclusion (Cartan_le_threeGroup E d hUT hf hX) z) v = v) : v = 0 := by
  apply m.equivalence.injective
  rw [map_zero]
  funext i
  apply SpecialLinearThreeCartanFixed.dual_fixed_eq_zero
    (layerField_large E) (layerField_predecessor_odd E) (layerCartan_card E hX)
    (layerCartanMap E d hX) (layerCartanMap_injective E d hX)
  intro z
  exact (a.lower_cartan_equivariant d hUT hf m hX z v i).symm.trans
    (congrArg (fun w => m.equivalence w i) (hv z))

end UpperActions
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
