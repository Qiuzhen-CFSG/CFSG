module

public import Theory.Representation.HexacodeAction.FullPlaneAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The full quotient on the six scalar planes

The scalar kernel fixes every full-weight plane. The resulting map from
the coordinate symmetric group to the permutations of these planes is
injective: a nontrivial normal kernel would contain A6, contradicting
the established alternating action on the planes. The equal six-letter
orders make it an isomorphism. This retains the literal plane action,
its exact cubic kernel, and its parity.

Source: the six-plane action in Aschbacher--Smith 12.7.10 and 12.7.18,
printed pp.842--845. No identification with the coordinate marking is
assumed.
-/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode

private theorem scalar_le_kernel : zpowers hexZ ≤ fullPlanePerm.ker := by
  apply zpowers_le.mpr
  change fullPlanePerm hexEvenZ.val = 1
  rw [fullPlanePerm_even, planePerm_scalar]

private def coordinatePlanes : Equiv.Perm (Fin 6) →* Equiv.Perm FullWeightScalarPlane :=
  hexCoordinateSixHom.liftOfSurjective hexCoordinateSix_surjective
    ⟨fullPlanePerm, by rw [hexCoordinateSix_kernel]; exact scalar_le_kernel⟩

private theorem coordinatePlanes_apply (g : HexAutomorphisms) :
    coordinatePlanes (hexCoordinateSixHom g) = fullPlanePerm g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

private theorem coordinatePlanes_injective : Function.Injective coordinatePlanes := by
  apply coordinatePlanes.ker_eq_bot_iff.mp
  by_contra hn
  have hA := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 6))
    ((nontrivial_iff_ne_bot _).mpr hn)
  have : Nontrivial (alternatingGroup FullWeightScalarPlane) :=
    alternatingGroup.nontrivial_of_three_le_card (by
      rw [Nat.card_eq_fintype_card, fullWeightScalarPlane_card]
      decide)
  obtain ⟨p, hp⟩ := exists_ne (1 : alternatingGroup FullWeightScalarPlane)
  obtain ⟨g, hg⟩ := planeAlternating_surjective p
  have hk := hA (hexEvenCoordinate g).property
  change coordinatePlanes (hexCoordinateSixHom g.val) = 1 at hk
  rw [coordinatePlanes_apply, fullPlanePerm_even] at hk
  apply hp
  apply Subtype.ext
  exact (congrArg Subtype.val hg).symm.trans hk

private theorem coordinatePlanes_bijective : Function.Bijective coordinatePlanes := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨coordinatePlanes_injective, ?_⟩
  simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
    fullWeightScalarPlane_card]

/-- The coordinate quotient and the actual plane quotient are related by an
isomorphism, with the action equation on every original hexacode actor. -/
theorem fullPlanePerm_coordinate_equiv :
    ∃ e : Equiv.Perm (Fin 6) ≃* Equiv.Perm FullWeightScalarPlane,
      ∀ g : HexAutomorphisms, e (hexCoordinateSixHom g) = fullPlanePerm g :=
  ⟨MulEquiv.ofBijective coordinatePlanes coordinatePlanes_bijective,
    coordinatePlanes_apply⟩

/-- The full actor induces all permutations of the literal six planes. -/
theorem fullPlanePerm_surjective : Function.Surjective fullPlanePerm := by
  intro p
  obtain ⟨q, hq⟩ := coordinatePlanes_bijective.2 p
  obtain ⟨g, rfl⟩ := hexCoordinateSix_surjective q
  exact ⟨g, (coordinatePlanes_apply g).symm.trans hq⟩

/-- The complete kernel of the six-plane action is the cubic scalar group. -/
theorem fullPlanePerm_kernel : fullPlanePerm.ker = zpowers hexZ := by
  rw [← hexCoordinateSix_kernel]
  ext g
  change fullPlanePerm g = 1 ↔ hexCoordinateSixHom g = 1
  rw [← coordinatePlanes_apply]
  exact ⟨fun hg => coordinatePlanes_injective (hg.trans (map_one _).symm),
    fun hg => hg ▸ map_one _⟩

/-- Parity on the six planes agrees with the intrinsic hexacode sign. -/
theorem fullPlanePerm_sign (g : HexAutomorphisms) :
    Equiv.Perm.sign (fullPlanePerm g) = hexSign g := by
  have : Nontrivial FullWeightScalarPlane := by
    apply Fintype.one_lt_card_iff_nontrivial.mp
    rw [fullWeightScalarPlane_card]
    decide
  have hs : Equiv.Perm.sign.comp coordinatePlanes = Equiv.Perm.sign :=
    Equiv.Perm.eq_sign_of_surjective_hom
      ((Equiv.Perm.sign_surjective FullWeightScalarPlane).comp coordinatePlanes_bijective.2)
  have he := DFunLike.congr_fun hs (hexCoordinateSixHom g)
  change Equiv.Perm.sign (fullPlanePerm g) = Equiv.Perm.sign (hexCoordinateSixHom g)
  simpa only [MonoidHom.comp_apply, coordinatePlanes_apply] using he

end Representation.Hexacode
