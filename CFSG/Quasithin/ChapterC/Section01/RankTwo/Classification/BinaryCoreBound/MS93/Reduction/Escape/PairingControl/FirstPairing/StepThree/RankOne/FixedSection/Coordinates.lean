module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne.FixedSection.Model

/-!
# Transporting the natural commutator into matrix coordinates

An equivariant natural coordinate map sends each group commutator to its
matrix displacement. Surjectivity supplies every displacement generator,
and the trivial kernel preserves cardinality. All subgroup inclusions use
the actual relative natural subgroup inside the local stabilizer.

Source: MS93 (4.3.2)(3), printed p.884.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne.FixedSection
variable {G : Type*} [Group G] {π : G →* SL} {U : Subgroup G}

/-- The actual group commutator maps onto the natural matrix displacement,
with the marking absorbed into the projection. -/
theorem natural_commutator_coordinates
    (u : RankOnePairing.NaturalFactor π ⊤ U ⊥) (T : Subgroup G) :
    ((⁅U, T⁆).subgroupOf U).map u.coordinates =
      matrixDisplacement (T.map (u.marking.toMonoidHom.comp π)) := by
  let e := u.marking.toMonoidHom.comp π
  let B := matrixDisplacement (T.map e)
  have hc (t : G) (x : U) :
      ∃ y : U, y.val = ⁅t, x.val⁆ ∧
        u.coordinates y = Multiplicative.ofAdd ((e t).val.mulVec
          (u.coordinates x).toAdd - (u.coordinates x).toAdd) := by
    let z : U := ⟨t * x.val * t⁻¹,
      le_normalizer_iff.mp u.normalized t (mem_top t) x.val x.property⟩
    refine ⟨z * x⁻¹, rfl, ?_⟩
    have hz := u.action t (mem_top t) x z rfl
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv]
    change (u.coordinates z).toAdd + -(u.coordinates x).toAdd = _
    rw [hz]
    simp only [toAdd_ofAdd, e, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, sub_eq_add_neg]
  have hcomm : ⁅U, T⁆ ≤ (B.comap u.coordinates).map U.subtype := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro t ht x hx
    obtain ⟨y, hy, he⟩ := hc t ⟨x, hx⟩
    refine ⟨y, ?_, hy⟩
    change u.coordinates y ∈ B
    rw [he]
    exact subset_closure ⟨e t, mem_map_of_mem e ht, (u.coordinates ⟨x, hx⟩).toAdd, rfl⟩
  apply le_antisymm
  · rintro v ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := hcomm hx
    have he' : y = x := Subtype.ext he
    subst y
    exact hy
  · change Subgroup.closure _ ≤ _
    apply (Subgroup.closure_le (k := _) (K := _)).mpr
    rintro v ⟨g, ⟨t, ht, rfl⟩, x, rfl⟩
    obtain ⟨z, hz⟩ := u.surjective (Multiplicative.ofAdd x)
    obtain ⟨y, hy, he⟩ := hc t z
    refine ⟨y, ?_, ?_⟩
    · change y.val ∈ ⁅U, T⁆
      rw [hy, commutator_comm]
      exact commutator_mem_commutator ht z.property
    · simpa only [hz, toAdd_ofAdd] using he

/-- Trivial coordinate kernel preserves the displacement order exactly. -/
theorem natural_commutator_card
    (u : RankOnePairing.NaturalFactor π ⊤ U ⊥) (T : Subgroup G) :
    Nat.card (matrixDisplacement (T.map (u.marking.toMonoidHom.comp π))) =
      Nat.card (⁅U, T⁆ : Subgroup G) := by
  rw [← natural_commutator_coordinates u T,
    card_map_of_injective u.equivOfBot.injective]
  apply Nat.card_congr
  exact (subgroupOfEquivOfLe (le_normalizer_iff_commutator_le_left.mp
    (le_top.trans u.normalized))).toEquiv

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne.FixedSection
