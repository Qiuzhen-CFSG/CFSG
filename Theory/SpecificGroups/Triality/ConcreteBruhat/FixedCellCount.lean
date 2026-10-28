module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedCellCount.Coordinates
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedDescent

/-!
# Cardinalities of the actual fixed triality Bruhat cells

The proved fixed normal form identifies each carrier Borel double coset with a
fixed positive factor, a fixed torus factor, and its supported Frobenius-fixed
right coordinates. The coordinate calculation gives q to the number of inverted
positive D4 roots. Summing over the twelve disjoint cells and cancelling the
nonzero Borel cardinality gives the Borel index, for every positive binary
exponent, including q = 2. No group-order formula or Sylow conclusion is an input.

The carrier and Borel are the original elementary central quotient and descended
subgroup. The comparison uses `FixedDescent.carrierNormalFormEquiv` and the
actual split-cell membership theorem, so no new model identification is assumed.

Source: GLS3 2.3.4–8 and §2.4, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open scoped BigOperators
namespace Triality.Standard.ConcreteBruhat.FixedCellCount
open Parabolics
noncomputable section

section Binary
variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn
local notation "D" => InputRealization.inputs P rfl

private theorem representative_twist (w : DihedralGroup 6) :
    (D).weylTwist (rootRepresentative w) = rootRepresentative w := by
  apply (D).lift_injective
  rw [← (D).graphField_lift]
  rw [FixedDescent.lift_rootRepresentative (binaryParameters n hn) (show (binaryParameters n hn).prime = 2 from rfl) w]
  exact (fixedSplitRepresentative P rfl w).property

abbrev CellFactors (w : DihedralGroup 6) :=
  (positiveSubgroup P).comap (fixedSubgroup P).subtype ×
  (splitTorus P).comap (fixedSubgroup P).subtype × FixedSupported P w

private def factorsNormalForm (w : DihedralGroup 6) (a : CellFactors n hn w) :
    SplitNormalForm.Coordinates P where
  left := ⟨a.1.val.val, a.1.property⟩
  torus := ⟨a.2.1.val.val, a.2.1.property⟩
  weyl := rootRepresentative w
  right := a.2.2.val.val
  supported := a.2.2.property

private theorem factorsNormalForm_fixed (w : DihedralGroup 6) (a : CellFactors n hn w) :
    SplitNormalForm.twist D (factorsNormalForm n hn w a) = factorsNormalForm n hn w a := by
  apply (SplitNormalForm.twist_eq_self_iff D _).mpr
  exact ⟨a.1.val.property, a.2.1.val.property, representative_twist n hn w,
    (PositiveCoordinates.twist_eq_self_iff P _).mp a.2.2.val.property⟩

private def factorsEquiv (w : DihedralGroup 6) :
    CellFactors n hn w ≃ {c : {c : SplitNormalForm.Coordinates P //
      SplitNormalForm.twist D c = c} // c.val.weyl = rootRepresentative w} where
  toFun a := ⟨⟨factorsNormalForm n hn w a, factorsNormalForm_fixed n hn w a⟩, rfl⟩
  invFun c := by
    have hf := (SplitNormalForm.twist_eq_self_iff D c.val.val).mp c.val.property
    exact (⟨⟨c.val.val.left.val, hf.1⟩, c.val.val.left.property⟩,
      ⟨⟨c.val.val.torus.val, hf.2.1⟩, c.val.val.torus.property⟩,
      ⟨⟨c.val.val.right, (PositiveCoordinates.twist_eq_self_iff P _).mpr hf.2.2.2⟩,
        by
          have h := c.val.val.supported
          rw [c.property] at h
          exact h⟩)
  left_inv a := rfl
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    exact SplitNormalForm.Coordinates.ext rfl rfl c.property.symm rfl

/-- The actual carrier cell, with fixed positive, torus, and inversion factors. -/
def cellEquiv (w : DihedralGroup 6) :
    CellFactors n hn w ≃ {g : Carrier P // g ∈ cell P rfl w} :=
  (factorsEquiv n hn w).trans
    ((FixedDescent.carrierNormalFormEquiv n hn).subtypeEquiv (fun c => by
      rw [FixedDescent.mem_cell_iff_split, FixedDescent.carrierToSplit_normalForm,
        SplitNormalForm.evaluate_mem_cell_iff]))

/-- Descent preserves the full positive fixed subgroup. -/
def unipotentFixedEquiv :
    unipotent P ≃ (positiveSubgroup P).comap (fixedSubgroup P).subtype :=
  (FixedDescent.carrierFixedEquiv P rfl).toEquiv.subtypeEquiv
    (fun g => FixedDescent.mem_descend_iff P rfl (positiveSubgroup P) g)

theorem card_unipotent : Nat.card (unipotent P) = (P).q ^ 12 := by
  rw [Nat.card_congr (unipotentFixedEquiv n hn)]
  exact PositiveCoordinates.card_fixedPositive_binary n hn

theorem card_borel : Nat.card (borel P) = (P).q ^ 12 * (((P).q ^ 3 - 1) * ((P).q - 1)) := by
  rw [← Nat.card_congr (borelEquiv P rfl), Nat.card_prod,
    card_unipotent n hn, TorusCoordinates.card_torus P rfl]

/-- Each actual double coset has |B| times the number of its inversion tuples. -/
theorem card_cell (w : DihedralGroup 6) :
    Nat.card {g : Carrier P // g ∈ cell P rfl w} =
      Nat.card (borel P) * (P).q ^ inversionCount w := by
  calc
    _ = Nat.card ((positiveSubgroup P).comap (fixedSubgroup P).subtype) *
        Nat.card ((splitTorus P).comap (fixedSubgroup P).subtype × FixedSupported P w) :=
      (Nat.card_congr (cellEquiv n hn w)).symm.trans (Nat.card_prod _ _)
    _ = (P).q ^ 12 * ((((P).q ^ 3 - 1) * ((P).q - 1)) * (P).q ^ inversionCount w) :=
      congrArg₂ (· * ·) (PositiveCoordinates.card_fixedPositive_binary n hn)
        ((Nat.card_prod _ _).trans (congrArg₂ (· * ·)
          (TorusCoordinates.card_fixedTorus P rfl) (card_fixedSupported P w)))
    _ = _ := (Nat.mul_assoc _ _ _).symm.trans
      (congrArg (fun k => k * (P).q ^ inversionCount w) (card_borel n hn).symm)

/-- The twelve cells form a disjoint partition of the original carrier. -/
def cellsEquiv : (Σ w : DihedralGroup 6, {g : Carrier P // g ∈ cell P rfl w}) ≃ Carrier P :=
  Equiv.ofBijective (fun a => a.2.val) (by
    constructor
    · rintro ⟨v, g⟩ ⟨w, h⟩ he
      change g.val = h.val at he
      have hw : v = w := FixedDescent.cell_index_unique n hn g.property (he.symm ▸ h.property)
      subst w
      exact congrArg (Sigma.mk v) (Subtype.ext he)
    · intro g
      obtain ⟨w, hw⟩ := FixedDescent.exists_mem_cell n hn g
      exact ⟨⟨w, ⟨g, hw⟩⟩, rfl⟩)

theorem card_carrier_sum :
    Nat.card (Carrier P) = Nat.card (borel P) * ∑ w : DihedralGroup 6, (P).q ^ inversionCount w := by
  rw [← Nat.card_congr (cellsEquiv n hn), Nat.card_sigma]
  simp only [card_cell n hn, Finset.mul_sum]

/-- Carrier cardinality derived from the proved fixed normal form. -/
theorem card_carrier : Nat.card (Carrier P) =
    Nat.card (borel P) * (((P).q ^ 3 + 1) * ((P).q + 1) * ((P).q ^ 8 + (P).q ^ 4 + 1)) := by
  rw [card_carrier_sum n hn, sum_inversion_powers]

/-- The Borel index in the original carrier, including q = 2. -/
theorem borel_index : (borel P).index =
    ((P).q ^ 3 + 1) * ((P).q + 1) * ((P).q ^ 8 + (P).q ^ 4 + 1) := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := borel P))
  rw [(borel P).card_mul_index, card_carrier n hn]

/-- The smallest binary parameter is included in the same normal-form count. -/
theorem borel_index_two : (borel (binaryParameters 1 (by decide))).index = 7371 := by
  rw [borel_index]
  norm_num [binaryParameters_q]

end Binary

/-- The parameter-independent characteristic-two version for downstream assembly. -/
theorem borel_index_of_char_two (P : Parameters) (hp : P.prime = 2) :
    (borel P).index = (P.q ^ 3 + 1) * (P.q + 1) * (P.q ^ 8 + P.q ^ 4 + 1) := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  exact borel_index n hn

end
end Triality.Standard.ConcreteBruhat.FixedCellCount
