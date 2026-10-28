module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.MSPair
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings

/-!
# The actual closure core has a nonsylow marked image

The full normalizer action of the original O₂(G₁) is contained in the
point-radical action. Restricting the original core to L and using the
faithful symplectic action on the complete chosen module transfers this
containment to its original marked quotient. The entire central attachment
of V remains in place during this comparison.

The conjugate point radical has order q³ and a symplectic Sylow subgroup
has order q⁴. Thus the literal original core image cannot be Sylow. This
supplies the nonsylow branch premise for the original-star field restriction.

Source: Aschbacher–Smith 11.5.7, pp.782–783, assertion (!).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open RadicalAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D) (m : MarkedFlag E)

/-- The actual core's component image lies in the actual marked local core.
The comparison uses the faithful action on all of V. -/
theorem original_core_marked_image_le_local_core (g : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap) :
    PointModel.image m (E.G₁.pCoreIn 2) ≤ PointModel.image m (E.L₁.pCoreIn 2) := by
  apply (map_le_map_iff_of_injective (FullAction.modelHom_injective m)).mp
  have hi : PointModel.image m (E.G₁.pCoreIn 2) =
      PointModel.image m (E.G₁.pCoreIn 2 ⊓ L) := by
    simp only [PointModel.image,inf_subgroupOf_right]
  rw [hi,FullAction.image_eq m _ inf_le_right,
    FullAction.image_eq m _ ((pCoreIn_le 2 E.L₁).trans E.L₁_le)]
  exact (image_mono (inf_le_left.trans (core_le_local_radical E m))).trans
    (FullAmbient.radical_image_le m g hp)

/-- The original marked core image has order at most q³, whereas every
symplectic Sylow has order q⁴. No nonsylow hypothesis is supplied. -/
theorem original_core_marked_image_not_sylow (g : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap) :
    ¬ ∃ S : Sylow 2 (Sp E.input.field.Carrier),
      (S : Subgroup (Sp E.input.field.Carrier)) = PointModel.image m (E.G₁.pCoreIn 2) := by
  rintro ⟨S,hS⟩
  have hcard : Nat.card (PointModel.image m (E.L₁.pCoreIn 2)) =
      Nat.card E.input.field.Carrier ^ 3 := by
    rw [PointModel.image_core m E.L₁ E.L₁_le,PointModel.local_identification m g hp,
      ←map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
      card_map_of_injective (MulAut.conj g).injective,
      PointRadicalAction.core_eq_radical E.input.field.card_eq E.input.nonbinary]
    exact SymplecticConjugatePair.card_pointRadical
  have hsyl : Nat.card S = Nat.card E.input.field.Carrier ^ 4 :=
    (Nat.card_congr (Sylow.equiv S
      (unipotentSylow E.input.field.card_eq (by have := E.input.nonbinary; omega))).toEquiv).trans
        card_unipotent
  have hle : (S : Subgroup (Sp E.input.field.Carrier)) ≤
      PointModel.image m (E.L₁.pCoreIn 2) := by
    rw [hS]
    exact original_core_marked_image_le_local_core E m g hp
  have hbound := card_le_of_le hle
  rw [hcard,hsyl] at hbound
  exact (not_le_of_gt (Nat.pow_lt_pow_right (Finite.one_lt_card :
    1 < Nat.card E.input.field.Carrier) (by decide : 3 < 4))) hbound

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
