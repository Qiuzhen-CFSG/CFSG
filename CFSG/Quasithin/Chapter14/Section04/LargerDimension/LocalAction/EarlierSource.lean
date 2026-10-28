module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.SourceGeometry
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags

/-!
# Assembling the earlier extraspecial inputs with the local geometry

The full-action proof constructs the hyperplane stabilizer, the escaping
cubic action and the selected component. Prime-index maximality then
identifies the two whole parabolics for each member of Y. Applying this to
L₁ and the surviving second member supplies the two linear vertex quotients;
the sibling model branches supply the middle S₃ × S₃ quotient. The ambient
intersection and residual-normalizer argument constructs the D-system on G₀.

The earlier inputs below are exactly the extraspecial clauses used by the
full-action producer. They remain to be instantiated by the source owners
of 12.8, 14.3 and 1.2.1. `NaturalFlagData` is an intermediate output
contract. `NaturalFlags.Construction` constructs it from `NaturalThreeAction`
and the actual flag; `NaturalFlags.Construction.Source` supplies it to this
assembly. The source-facing endpoint in `LocalAction.Source` retains only
the authorized earlier and sibling inputs.

Source: Aschbacher--Smith, 14.4.8 and the geometry in 14.4.13,
printed pp.1009,1012. The final recognition belongs to the outer source owner.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
open Components
variable {G : Type*} [Group G] [Finite G]

/-- Earlier extraspecial geometry: 12.8.8(1), 12.8.9(1--2) and
12.8.11(2),(4), in the precise ambient subgroups used by 14.4.8.
No full moved-space action, component or parabolic conclusion is a field. -/
structure EarlierExtraspecialData (T : Sylow 2 G)
    (V₂ E U Ug Z Zg Wg L₂ : Subgroup G) : Prop where
  V₂_le_T : V₂ ≤ T
  T_normalizes_V₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G)
  U_le_T : U ≤ T
  Wg_le_T : Wg ≤ T
  Wg_le_Ug : Wg ≤ Ug
  E_le : E ≤ U ⊓ Ug
  U_commutator : ⁅U, U⁆ ≤ Z
  Ug_commutator : ⁅Ug, Ug⁆ ≤ Zg
  U_center : U ⊓ centralizer (U : Set G) = Z
  Z_card : Nat.card Z = 2
  Zg_card : Nat.card Zg = 2
  V₂_card : Nat.card V₂ = 4
  plane : V₂ = Z ⊔ Zg
  fixed : ∀ D : Subgroup G, D ≤ E → ⁅D, Wg⁆ ≤ Z → D ≤ V₂
  supplement : U ⊔ Ug = L₂ ⊔ U
  plane_normalizes : U ⊔ Ug ≤ normalizer (V₂ : Set G)
  plane_image_card : Nat.card (conjugation (U ⊔ Ug) V₂ plane_normalizes).range = 6
  plane_centralizer : Wg ≤ centralizer (V₂ : Set G)

/-- Construct the literal action for an arbitrary Y-member from the earlier
source inputs. This also retains the marked quotient formulas in the output. -/
theorem full_action_of_earlier_data
    (earlier : EarlierComponentGeneration G)
    (T : Sylow 2 G) (hEven : IsEvenCharacteristicAt T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    {H K V₂ E X U Ug Z Zg Wg L₂ : Subgroup G} [IsElementaryAbelian 2 E]
    (d : EarlierExtraspecialData T V₂ E U Ug Z Zg Wg L₂)
    (hX : X ∈ YFamily H T V₂ E) (h₂ : ThreeExtension K T L₂) :
    Nonempty (FullMovedSpaceAction T (U ⊔ Ug) L₂ V₂ X) := by
  exact full_moved_space_action earlier T hEven classification hX
    d.V₂_le_T d.T_normalizes_V₂ d.U_le_T d.Wg_le_T d.Wg_le_Ug d.E_le
    d.U_commutator d.Ug_commutator d.U_center d.Z_card d.Zg_card d.V₂_card
    d.plane d.fixed d.supplement d.plane_normalizes d.plane_image_card d.plane_centralizer
    h₂.residual_eq h₂.coreQuotient_card h₂.T_normalizes

/-- The output of the conditional local assembly. The full action and all
parabolic clauses hold for every Y-member, independently of the subsequent
choice of the surviving second member used for the three-vertex geometry. -/
structure EarlierSourceResult (H M L L₁ L₂ V₂ E U Ug X : Subgroup G) (T : Sylow 2 G) where
  action : ∀ Y : Subgroup G, Y ∈ YFamily H T V₂ E →
    FullMovedSpaceAction T (U ⊔ Ug) L₂ V₂ Y
  parabolics : ∀ Y : Subgroup G, Y ∈ YFamily H T V₂ E →
    Quasithin.I5.RankTwoParabolics (localJoin L₂ Y ⊔ (T : Subgroup G) : Subgroup G)
      ((T : Subgroup G).subgroupOf (localJoin L₂ Y ⊔ (T : Subgroup G)))
      ((U ⊔ Ug ⊔ (T : Subgroup G)).subgroupOf (localJoin L₂ Y ⊔ (T : Subgroup G)))
      ((Y ⊔ (T : Subgroup G)).subgroupOf (localJoin L₂ Y ⊔ (T : Subgroup G)))
  geometry : SourceGeometry L L₁ L₂ X M T

/-- Assemble the action, parabolics and intrinsic A₃ geometry. Besides the
explicit earlier inputs, the only later branch input is the middle quotient
for a distinct second Y-member. No marked maximality or geometric output is
assumed. `NaturalFlags.naturalFlagData_of_invariant_flag` constructs hN from
the earlier natural action and the literal invariant flag. -/
noncomputable def source_geometry_of_earlier_data
    (earlier : EarlierComponentGeneration G)
    (T : Sylow 2 G) (hEven : IsEvenCharacteristicAt T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    {H M L L₁ L₂ V₁ V₂ V E X U Ug Z Zg Wg : Subgroup G} [IsElementaryAbelian 2 E]
    (d : EarlierExtraspecialData T V₂ E U Ug Z Zg Wg L₂)
    (hN : NaturalFlagData H T V₁ V₂ V E L L₁ L₂)
    (hX : X ∈ YFamily H T V₂ E) (hne : X ≠ L₁)
    (e₂ : coreQuotient (L₁ ⊔ X ⊔ (T : Subgroup G)) ≃* SymmetricThreeProduct.G)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → L ⊔ (T : Subgroup G) ≤ K → K = M)
    (hLM : L ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hMnorm : M ≤ normalizer (L : Set G)) :
    EarlierSourceResult H M L L₁ L₂ V₂ E U Ug X T := by
  let action (Y : Subgroup G) (hY : Y ∈ YFamily H T V₂ E) :=
    (full_action_of_earlier_data earlier T hEven classification d hY hN.L₂_three).some
  have h₁ : L₁ ∈ YFamily H T V₂ E := by
    refine ⟨hN.L₁_three, ?_, ?_⟩
    · rw [hN.moved_eq, hN.moved_card]
    · rw [hN.moved_eq]
      exact hN.moved_le_E
  exact {
    action := action
    parabolics := fun Y hY => (action Y hY).parabolics hY hN.L₂_three d.supplement d.U_le_T
    geometry := source_geometry_of_full_actions H M L L₁ L₂ V₁ V₂ V E X (U ⊔ Ug) T
      hN hX hne (action L₁ h₁) (action X hX) e₂ hunique hLM hTM hMnorm }

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
