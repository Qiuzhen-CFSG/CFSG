module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Stellmacher.Recognition.NormalFourNonnormalCyclicWeakClosure
public import Stellmacher.Recognition.NormalFourNonnormalCyclicOuterCentralizer
public import Stellmacher.Recognition.SimpleInvolutionFusion
public import Theory.GroupTheory.PGroup.ExtraspecialCentralProductOrder
public import Theory.GroupTheory.WeaklyClosedSquareFusion

/-!
# Cyclic-tail exclusion in the nonnormal four-group branch

In a Hall decomposition of the actual quotient two-core, a nontrivial
cyclic tail is the whole core center. For an extraspecial factor of order
eight, the original core preimage has four times the order of that tail.

The fusion assembly below separates the two ambient inputs needed to
exclude a large cyclic tail: weak closure of the central involution in the
core preimage, and an elementary eight arising from a conjugate outside
that preimage. Z-star supplies that outside conjugate. The final theorem
discharges both local inputs using the cyclic-tail weak-closure theorem
and its extension from the unique normal four to the Sylow subgroup.
No core-order or Sylow-index upper bound is assumed. Neither the width
exclusion nor Sylow noncommutativity is needed for this cyclic-tail bound.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, Case 2, p.393.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial cyclic Hall tail is precisely the center of the actual core. -/
public theorem omegaQuotient_cyclic_tail_eq_center
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (E : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] [IsCyclic D] (hD : D ≠ ⊥)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hgen : A ⊔ D = ⊤) : D = center (pCore 2 (OmegaQuotient S)) := by
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic hrank S E hunique hnormal
  exact (center_eq_cyclic_factor_of_extraspecial_of_cyclic_center
    pCore_isPGroup A D hD hc hgen).symm

/-- The actual core preimage has four times the order of a nontrivial
commuting tail when the extraspecial factor has order eight. -/
public theorem card_omegaCorePreimage_eq_four_mul_tail
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (E : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hA : Nat.card A = 8) (hD : D ≠ ⊥)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hgen : A ⊔ D = ⊤) : Nat.card (omegaCorePreimage S) = 4 * Nat.card D := by
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic hrank S E hunique hnormal
  have h := card_mul_two_eq_of_extraspecial_of_cyclic_center
    pCore_isPGroup A D hD hc hgen
  rw [hA] at h
  rw [card_omegaCorePreimage]
  omega

/-- Weak closure in the core forces the distinct Sylow conjugate supplied
by Z-star to lie outside the actual core preimage. -/
public theorem exists_conjugate_outside_omegaCorePreimage
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (S : Sylow 2 G) (z : S) (hz : orderOf z = 2)
    (hweak : ∀ t : S, t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z) :
    ∃ t : S, t ∉ omegaCorePreimage S ∧ IsConj (z : G) (t : G) := by
  obtain ⟨t, hne, hconj⟩ := exists_distinct_isConj_in_sylow hns S z hz
  exact ⟨t, fun ht => hne (hweak t ht hconj), hconj⟩

/-- Assemble the cyclic-tail bound once the two local fusion steps have
been established. An elementary eight already contradicts the rank bound,
so the later automizer argument of the source is unnecessary. -/
public theorem omegaQuotient_cyclic_tail_card_lt_eight_of_local_fusion
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (D : Subgroup (pCore 2 (OmegaQuotient S)))
    (hweak : 8 ≤ Nat.card D → ∀ z t : S, z ∈ center S → orderOf z = 2 →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z)
    (houter : 8 ≤ Nat.card D → ∀ z t : S, z ∈ center S → orderOf z = 2 →
      t ∉ omegaCorePreimage S → IsConj (z : G) (t : G) →
      ∃ U : Subgroup S, IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U) :
    Nat.card D < 8 := by
  by_contra! hlarge
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let z : S := (w : center S)
  have hz : orderOf z = 2 := (orderOf_coe (w : center S)).trans
    ((orderOf_coe w).trans hw)
  have hzC : z ∈ center S := (w : center S).property
  obtain ⟨t, ht, hconj⟩ := exists_conjugate_outside_omegaCorePreimage hns S z hz
    (fun t => hweak hlarge z t hzC hz)
  obtain ⟨U, hU, hcard⟩ := houter hlarge z t hzC hz ht hconj
  exact (not_lt_of_ge hcard)
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G) U hU)

/-- A cyclic Hall tail commuting with an extraspecial factor of order eight
has order less than eight. The local fusion inputs are discharged in the
actual core preimage, without any assumed core-order or Sylow-index bound. -/
public theorem omegaQuotient_cyclic_tail_card_lt_eight
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] [IsCyclic D] (hA : Nat.card A = 8)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hgen : A ⊔ D = ⊤) : Nat.card D < 8 := by
  have hweak := omegaCorePreimage_weakly_closed_of_large_cyclic_tail
    hN hrank S hZ E hE hunique hnormal A D hA hc hgen
  apply omegaQuotient_cyclic_tail_card_lt_eight_of_local_fusion hns hrank S hZ D hweak
  intro hlarge
  exact exists_elementary_eight_of_conjugate_outside_omegaCorePreimage
    hN hrank S hZ E hE hunique (hweak hlarge)

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
