module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Stellmacher.Recognition.NormalFourNonnormalCyclicTail
public import Stellmacher.Recognition.NormalFourNonnormalNoncyclicTail
public import Theory.GroupTheory.PGroup.RankTwoSymplecticBounds
public import Theory.GroupTheory.PGroup.ExtraspecialCentralProductOrder

/-!
# Width-one core bound for the nonnormal four-group branch

Work in the actual odd-core quotient of the central-omega normalizer.
Excluding every Hall decomposition with an extraspecial factor of order
thirty-two makes the extraspecial factors have order eight. The core has
cyclic center, so a nontrivial Hall tail meets such a factor in order two;
the whole core therefore has four times the order of the tail.

The ambient fusion exclusions for cyclic and noncyclic tails each bound the
tail order strictly below eight, giving core order strictly below thirty-two.
The final theorem discharges these exclusions from ambient simplicity and
the local hypotheses. An order-eight displayed factor by itself does not
exclude alternative decompositions of width two; the explicit width
exclusion is retained throughout.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, pp.392–393, Cases 1 and 2.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- Width exclusion reduces the Hall factors to an extraspecial order-eight
factor and a nontrivial commuting tail, with the exact order formula. -/
public theorem omegaQuotient_pCore_factors_of_width_exclusion (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hwidth : ∀ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal → D.Normal → IsExtraspecial 2 A → IsBinaryHallFactor D →
      D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) → A ⊔ D = ⊤ →
      Nat.card A ≠ 32) :
    ∃ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal ∧ D.Normal ∧ IsExtraspecial 2 A ∧ Nat.card A = 8 ∧
      IsBinaryHallFactor A ∧ IsBinaryHallFactor D ∧ D ≠ ⊥ ∧
      D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) ∧ A ⊔ D = ⊤ ∧
      Nat.card (pCore 2 (OmegaQuotient S)) = 4 * Nat.card D := by
  obtain ⟨A, D, hAn, hDn, hA, hmodel, _, hD, hc, hgen⟩ :=
    omegaQuotient_pCore_factors hN hrank S hZ E hE hunique hnormal
  have hAc : Nat.card A = 8 ∧ IsBinaryHallFactor A :=
    hmodel.card_eight_hall_or_thirty_two.resolve_right
      (hwidth A D hAn hDn hA hD hc hgen)
  have hDne : D ≠ ⊥ := by
    intro hDbot
    have hAtop : A = ⊤ := by simpa only [hDbot, sup_bot_eq] using hgen
    exact omegaQuotient_pCore_not_hall hN hrank S hZ E hE hnormal
      (hAc.2.of_mulEquiv ((MulEquiv.subgroupCongr hAtop).trans Subgroup.topEquiv))
  let : A.Normal := hAn
  let : D.Normal := hDn
  let : IsExtraspecial 2 A := hA
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic hrank S E hunique hnormal
  have hcard := card_mul_two_eq_of_extraspecial_of_cyclic_center
    pCore_isPGroup A D hDne hc hgen
  rw [hAc.1] at hcard
  exact ⟨A, D, hAn, hDn, hA, hAc.1, hAc.2, hD, hDne, hc, hgen, by omega⟩

/-- The two ambient tail exclusions suffice for the required core bound.
Both exclusions refer to the same genuine Hall decomposition of the core. -/
public theorem omegaQuotient_pCore_card_lt_thirty_two_of_tail_bounds (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hwidth : ∀ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal → D.Normal → IsExtraspecial 2 A → IsBinaryHallFactor D →
      D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) → A ⊔ D = ⊤ →
      Nat.card A ≠ 32)
    (hcyclic : ∀ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal → D.Normal → IsExtraspecial 2 A → Nat.card A = 8 →
      IsCyclic D → D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) →
      A ⊔ D = ⊤ → Nat.card D < 8)
    (hnoncyclic : ∀ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal → D.Normal → IsExtraspecial 2 A → Nat.card A = 8 →
      IsBinaryHallFactor D → ¬ IsCyclic D →
      D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) →
      A ⊔ D = ⊤ → Nat.card D < 8) :
    Nat.card (pCore 2 (OmegaQuotient S)) < 32 := by
  obtain ⟨A, D, hAn, hDn, hA, hAc, _, hD, _, hc, hgen, hcard⟩ :=
    omegaQuotient_pCore_factors_of_width_exclusion hN hrank S hZ E hE hunique hnormal hwidth
  have hsmall : Nat.card D < 8 := by
    by_cases hDc : IsCyclic D
    · exact hcyclic A D hAn hDn hA hAc hDc hc hgen
    · exact hnoncyclic A D hAn hDn hA hAc hD hDc hc hgen
  omega

/-- Intrinsic width one bounds the quotient two-core strictly below order
thirty-two. The cyclic and noncyclic ambient fusion exclusions discharge
both tail bounds, without any core-order or Sylow-index upper bound. -/
public theorem omegaQuotient_pCore_card_lt_thirty_two_of_width_exclusion
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hwidth : ∀ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal → D.Normal → IsExtraspecial 2 A → IsBinaryHallFactor D →
      D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) → A ⊔ D = ⊤ →
      Nat.card A ≠ 32) :
    Nat.card (pCore 2 (OmegaQuotient S)) < 32 := by
  apply omegaQuotient_pCore_card_lt_thirty_two_of_tail_bounds
    hN hrank S hZ E hE hunique hnormal hwidth
  · intro A D hAn hDn hA hAc hDc hc hgen
    let : A.Normal := hAn
    let : D.Normal := hDn
    let : IsExtraspecial 2 A := hA
    let : IsCyclic D := hDc
    exact omegaQuotient_cyclic_tail_card_lt_eight
      hns hN hrank S hZ E hE hunique hnormal A D hAc hc hgen
  · intro A D hAn hDn hA hAc hD hDc hc hgen
    let : A.Normal := hAn
    let : D.Normal := hDn
    let : IsExtraspecial 2 A := hA
    exact omegaQuotient_noncyclicHallTail_card_lt_eight
      hns hN hrank S hnonab hZ E hE hunique hnormal hwidth A D hAc hD hDc hc hgen

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
