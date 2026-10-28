module

public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.Source
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.CommutingFactorsOddRank
public import Theory.GroupTheory.GeneralizedFitting.PrimeCoreNormalized
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# The number of actual χ-blocks

Every χ-block contains a cubic element and has a two-group center. The
guarded block-commutation theorem therefore embeds an independent cubic
group for each distinct block. In characteristic two its guard follows
from normal-subgroup inheritance. Thus the entire family of χ-blocks,
not just a selected decomposition, has size at most the three-rank.

Source: Aschbacher–Smith, C.1.9 and C.1.28, printed pp.123 and133–134.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

private theorem three_dvd_slTwo {F : Type*} [Field F] [Finite F] :
    3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [Atlas.card_sl_two]
  let q := Nat.card F
  change 3 ∣ q * (q ^ 2 - 1)
  by_cases hq : q % 3 = 0
  · exact dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero hq) _
  · have hmod : q % 3 = 1 ∨ q % 3 = 2 := by omega
    have hs : (q ^ 2) % 3 = 1 := by
      rcases hmod with hm | hm <;> simp [pow_two, Nat.mul_mod, hm]
    exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero (by omega)) _

/-- The literal natural actor of each χ-block has order divisible by three. -/
theorem three_dvd_card_of_chi {L : Type*} [Group L] [Finite L]
    (h : IsChiBlock L) : 3 ∣ Nat.card L := by
  have hq : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rcases h with ⟨n, _, _, F, _, _, _, _, hm⟩ | ⟨n, _, hn, _, hm⟩
    · obtain ⟨e⟩ := hm.quotient_iso
      rw [Nat.card_congr e.toEquiv]
      exact three_dvd_slTwo
    · obtain ⟨e⟩ := hm.quotient_iso
      rw [Nat.card_congr e.toEquiv]
      let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
      have hd : 3 ∣ 2 * Nat.card (alternatingGroup (Fin n)) := by
        rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
        exact Nat.dvd_factorial (by decide) hn
      exact (Nat.prime_three.dvd_mul.mp hd).resolve_left (by decide)
  exact hq.trans (Subgroup.card_quotient_dvd_card (pCore 2 L))

/-- A short group has a two-group center by its actual Fitting equality. -/
theorem center_isTwoGroup_of_short {L : Type*} [Group L] [Finite L]
    (h : IsShort L) : IsPGroup 2 (center L) := by
  apply (pCore_isPGroup (p := 2) (G := L)).to_le
  have hc : centralizer (pCore 2 L : Set L) ≤ pCore 2 L := by
    rw [← h.fitting]
    exact centralizer_generalizedFitting_le L
  exact (center_le_centralizer _).trans hc

/-- Characteristic two supplies exactly the published guard in C.1.9. -/
theorem blockCommutationHypothesis_of_fitting
    (h : generalizedFitting G = pCore 2 G) : BlockCommutationHypothesis G := by
  intro _
  let N := upperTwoThreeCore G
  let : N.Normal := inferInstanceAs
    ((pCore 3 (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G))).Normal
  exact generalizedFitting_eq_pCore_of_normalized_by_pCore N h le_normalizer_of_normal

/-- Any family of distinct actual χ-blocks contributes its cardinality to
the original group's three-rank. -/
theorem card_le_threeRank {I : Type*} [Fintype I]
    (hG : BlockCommutationHypothesis G) (L : I → Subgroup G)
    (hinj : Function.Injective L) (hL : ∀ i, IsChiBlockIn (L i)) :
    Fintype.card I ≤ primeRank 3 G := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  choose x hx using fun i => exists_prime_orderOf_dvd_card' (G := L i) 3
    (three_dvd_card_of_chi (hL i).2)
  exact Subgroup.card_le_primeRank_of_commuting_factors L (by decide)
    (fun i j hij => commutator_eq_bot_iff_le_centralizer.mp
      (blocks_commute hG (hL i).1 (hL j).1 (fun h => hij (hinj h))))
    (fun i => center_isTwoGroup_of_short (hL i).1.short) x hx

/-- The complete family of χ-blocks has at most two members in the source
three-rank range; no decomposition has been assumed. -/
theorem card_chiBlocks_le_two (hG : generalizedFitting G = pCore 2 G)
    (hr : primeRank 3 G ≤ 2) :
    Nat.card {L : Subgroup G // IsChiBlockIn L} ≤ 2 := by
  classical
  let I := {L : Subgroup G // IsChiBlockIn L}
  let : Fintype I := Fintype.ofFinite I
  rw [Nat.card_eq_fintype_card]
  exact (card_le_threeRank (blockCommutationHypothesis_of_fitting hG)
    (fun i : I => i.val) Subtype.val_injective (fun i => i.property)).trans hr

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct
