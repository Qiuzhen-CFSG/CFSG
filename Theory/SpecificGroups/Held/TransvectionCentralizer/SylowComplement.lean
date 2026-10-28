module
public import Theory.SpecificGroups.Held.TransvectionCentralizer.ComplementData
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SeedIdentification
import all Theory.SpecificGroups.Held.TransvectionCentralizer.ComplementData
import all Theory.SpecificGroups.Held.AutomorphismLocalPair.SeedIdentification

/-! The checked word table gives an actual complement, inside the original
Held Sylow subgroup, to its literal normal elementary subgroup of order 16. -/

namespace Held.TransvectionCentralizer.SylowComplement
open Subgroup LocalPairs.SylowGeometry.Calculations
open TwoLocalCandidates.MaximalNormalizerCatalogue
open IntrinsicEnumeration ExtensionChecks

private theorem normalForm_injective : Function.Injective normalForm := by
  apply (normalForm_surjective.bijective_of_nat_card_le ?_).1
  simpa only [Nat.card_fin] using
    InnerNormalizer.representative_card_ge_of_orbit_labels
      InnerNormalizer.orbitSizeLabel_eq_card_orbit

private theorem normalForm_zero : normalForm 0 = 1 := by
  apply Subtype.ext
  apply Held.eq_of_four_point_images
  rw [← normalFormAction_eq]
  decide +kernel

private theorem product_identity (i j : Fin 64) :
    normalForm (index (productIndex i j)) = normalForm (index i) * normalForm (index j) := by
  apply same_eq_true.mp
  simpa only [same, sameAction, normalFormAction_eq, Subgroup.coe_mul, map_mul] using
    multiplication_check i j

private theorem inverse_identity (i : Fin 64) :
    normalForm (index (inverseIndex i)) = (normalForm (index i))⁻¹ := by
  apply mul_eq_one_iff_eq_inv.mp
  apply same_eq_true.mp
  simpa only [same, sameAction, normalFormAction_eq, Subgroup.coe_mul, Subgroup.coe_one,
    map_mul, map_one] using inverse_check i

private def complement : Subgroup representative where
  carrier := Set.range (fun i : Fin 64 => normalForm (index i))
  one_mem' := ⟨0, normalForm_zero⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨productIndex i j, product_identity i j⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨inverseIndex i, inverse_identity i⟩

private theorem complement_card : Nat.card complement = 64 := by
  let f : Fin 64 → complement := fun i => ⟨normalForm (index i), ⟨i, rfl⟩⟩
  have hf : Function.Bijective f := ⟨fun i j he => index_injective
    (normalForm_injective (congrArg Subtype.val he)), by
      rintro ⟨x, i, rfl⟩; exact ⟨i, rfl⟩⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans (Nat.card_fin 64)

public theorem row_nine_elementary : IsElementaryAbelian 2 (entry 9) :=
  AutomorphismLocalPair.elementary_of_check 9 (by decide +kernel)

public theorem row_nine_card : Nat.card (entry 9) = 16 := by
  rw [AutomorphismLocalPair.entry_card]
  decide +kernel

/-- The complement is a subgroup of the original native Sylow carrier. -/
public theorem exists_complement : ∃ L : Subgroup representative, (entry 9).IsComplement' L := by
  refine ⟨complement, isComplement'_of_card_mul_and_disjoint ?_ ?_⟩
  · rw [row_nine_card, complement_card]
    have hc := Nat.card_congr (Equiv.ofBijective normalForm
      ⟨normalForm_injective, normalForm_surjective⟩)
    simpa only [Nat.card_fin] using hc
  · apply disjoint_def.mpr
    rintro x hx ⟨i, rfl⟩
    obtain ⟨m, hm, he⟩ := (certified_members (some 9) _).mp hx
    have hi : index i ∈ members (some 9) := normalForm_injective he ▸ hm
    change normalForm (index i) = 1
    rw [disjoint_check i hi, normalForm_zero]

end Held.TransvectionCentralizer.SylowComplement
