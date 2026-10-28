module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.Projection
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Odd-core control using the normal central four

Every normal odd subgroup of the extended centralizer commutes with its
normal subgroup inherited from Z(L). An order bound of 144 on that centralizer
therefore bounds the odd core by nine. The already constructed normal E₉
residual gives equality.

This conditional alternative to a full GL₂(3) action requires a calculation
only in the centralizer of the actual covering kernel. The numerical bound
remains explicit and must be established from the four-cover model.

Source: Aschbacher--Smith, 15.3.38, printed pp.1136--1137, manuscript of
1 March 2004.
-/

public section
namespace Matrix.PSL3Four.ExtendedCentralizer
open Subgroup
variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]

/-- The part of the central four in the actual involution centralizer. -/
@[expose] def centralFourIn (w : I) : Subgroup (centralizerIn w) :=
  ((center L).map L.subtype).comap (centralizerIn w).subtype

/-- The centralizer of that normal two-group, relative to C_I(w). -/
@[expose] def centerCentralizerIn (w : I) : Subgroup (centralizerIn w) :=
  centralizer (centralFourIn (L := L) w : Set (centralizerIn w))

theorem centralFourIn_normal (d : Overgroup L) (w : I) :
    (centralFourIn (L := L) w).Normal := by
  change (((center L).map L.subtype).comap (centralizerIn w).subtype).Normal
  rw [← d.projectiveAction_ker]
  infer_instance

theorem centralFourIn_card_dvd (d : Overgroup L) (w : I) :
    Nat.card (centralFourIn (L := L) w) ∣ 4 := by
  have hd := card_comap_dvd_of_injective ((center L).map L.subtype)
    (centralizerIn w).subtype (centralizerIn w).subtype_injective
  rw [card_map_of_injective L.subtype_injective] at hd
  let := d.cover.center_isKleinFour
  simpa only [centralFourIn, IsKleinFour.card_four] using hd

variable [Finite I]

/-- Normal odd subgroups centralize the normal part of the covering kernel. -/
theorem oddCore_le_centerCentralizer (d : Overgroup L) (w : I) :
    pPrimeCore 2 (centralizerIn w) ≤ centerCentralizerIn (L := L) w := by
  let := centralFourIn_normal d w
  have hc : Nat.Coprime (Nat.card (pPrimeCore 2 (centralizerIn w)))
      (Nat.card (centralFourIn (L := L) w)) :=
    ((pPrimeCore_coprime_card (p := 2) (G := centralizerIn w)).symm.pow_right 2).of_dvd_right
      (centralFourIn_card_dvd d w)
  exact commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_disjoint (disjoint_of_coprime_natCard hc))

/-- The source odd-core identification only needs a bound on the centralizer
of the covering kernel. Full GL₂(3) action is unnecessary for this step. -/
theorem oddCore_eq_residual_of_centerCentralizer_card_dvd (d : Overgroup L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine)
    (hcard : Nat.card (centerCentralizerIn (L := L) w) ∣ 144) :
    pPrimeCore 2 (centralizerIn w) = residualIn (L := L) w := by
  have hd : Nat.card (pPrimeCore 2 (centralizerIn w)) ∣ 144 :=
    (card_dvd_of_le (oddCore_le_centerCentralizer d w)).trans hcard
  have h9 : Nat.card (pPrimeCore 2 (centralizerIn w)) ∣ 9 :=
    ((pPrimeCore_coprime_card (p := 2) (G := centralizerIn w)).symm.pow_right 4).dvd_of_dvd_mul_left hd
  apply Eq.symm
  apply eq_of_le_of_card_ge (residualIn_le_oddCore w e)
  rw [residualIn_card w e]
  exact Nat.le_of_dvd (by decide) h9

end Matrix.PSL3Four.ExtendedCentralizer
