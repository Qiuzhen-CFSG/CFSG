module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Theory.GroupTheory.InvolutionPowerFusion
public import Theory.GroupTheory.PGroup.ExtraspecialCentralProductPowers
public import Theory.GroupTheory.PGroup.LargeBinaryHallRotations

/-!
# Restricted weak closure for the large Hall tail

Squares in a cyclic subgroup of the quotient two-core put fourth powers
of the original Sylow group in a cyclic subgroup, provided the core
preimage has index at most two. Commuting fourth roots in normal four-groups
then exclude fusion of the central involution inside the given four.

A noncyclic Hall factor of order at least sixteen supplies a rotation whose
order is divisible by eight. The intrinsic central-product calculation gives
both the cyclic-square subgroup and the commuting fourth roots, completing
the restricted weak-closure argument without an extraspecial order bound.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, Case 1, p.392.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Intrinsic cyclic-square and commuting-root data in the actual quotient
core exclude central-involution fusion in the normal four. -/
public theorem eq_of_isConj_in_four_of_core_power_data
    (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hi : (omegaCorePreimage S).index ≤ 2)
    (R : Subgroup (pCore 2 (OmegaQuotient S))) [IsCyclic R]
    (hsquares : ∀ x : pCore 2 (OmegaQuotient S), x ^ 2 ∈ R)
    (hroots : ∀ F : Subgroup (pCore 2 (OmegaQuotient S)),
      F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 →
      ∀ z t : pCore 2 (OmegaQuotient S), z ∈ center (pCore 2 (OmegaQuotient S)) →
        orderOf z = 2 → t ∈ F → ∃ x : pCore 2 (OmegaQuotient S),
          x ^ 4 = z ∧ Commute x t)
    (z t : S) (hzc : z ∈ center S) (hz : orderOf z = 2)
    (htE : t ∈ E) (hconj : IsConj (z : G) (t : G)) : t = z := by
  let H := omegaCorePreimage S
  let e := omegaCorePreimageEquiv S
  have hEH : E ≤ H := four_le_omegaCorePreimage hN hrank S hZ E hE
  have hzE : z ∈ E := by
    apply mem_four_of_square_eq_one_of_elementary_card_lt_eight
      (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) E hE
    · simpa only [hz] using pow_orderOf_eq_one z
    · exact center_le_centralizer _ hzc
  let zH : H := ⟨z, hEH hzE⟩
  let tH : H := ⟨t, hEH htE⟩
  let F := (E.subgroupOf H).map e.toMonoidHom
  let : IsElementaryAbelian 2 (E.subgroupOf H) := IsElementaryAbelian.subgroupOf hEH
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map _
  let : F.Normal := (inferInstance : (E.subgroupOf H).Normal).map _ e.surjective
  have hF : Nat.card F = 4 := by
    rw [card_map_of_injective e.injective]
    exact (Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv).trans hE
  have hzC : e zH ∈ center (pCore 2 (OmegaQuotient S)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨u, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (mem_center_iff.mp hzc (u : S)))
  have hzO : orderOf (e zH) = 2 := by
    rw [e.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hz
  have htF : e tH ∈ F := mem_map_of_mem e.toMonoidHom htE
  obtain ⟨x, hx, hxt⟩ := hroots F inferInstance inferInstance hF
    (e zH) (e tH) hzC hzO htF
  let R' := R.comap e.toMonoidHom
  let : IsCyclic R' := isCyclic_of_injective (e.toMonoidHom.subgroupComap R) (by
    intro a b h
    exact Subtype.ext (e.injective (congrArg Subtype.val h)))
  have hsq (u : H) : u ^ 2 ∈ R' := by
    change e (u ^ 2) ∈ R
    rw [map_pow]
    exact hsquares (e u)
  have hroot : ∃ u : H, u ^ 4 = zH ∧ Commute u tH := by
    refine ⟨e.symm x, ?_, ?_⟩
    · apply e.injective
      rw [map_pow, e.apply_symm_apply, hx]
    · have hh := hxt.map e.symm.toMonoidHom
      change Commute (e.symm x) (e.symm (e tH)) at hh
      rwa [e.symm_apply_apply] at hh
  have heq := S.eq_of_isConj_of_index_le_two_of_squares_mem_cyclic H hi R' hsq
    zH hzc ((Subgroup.orderOf_coe zH).symm.trans hz) tH hroot hconj
  exact congrArg Subtype.val heq

/-- A large noncyclic Hall tail excludes central-involution fusion inside the
normal four, provided the actual core preimage has index at most two.
No width bound or prescribed order of the extraspecial factor is needed. -/
public theorem eq_of_isConj_in_four_of_large_noncyclic_tail
    (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hi : (omegaCorePreimage S).index ≤ 2)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hD : IsBinaryHallFactor D) (hnc : ¬ IsCyclic D)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hg : A ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (z t : S) (hzc : z ∈ center S) (hz : orderOf z = 2)
    (htE : t ∈ E) (hconj : IsConj (z : G) (t : G)) : t = z := by
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic hrank S E hunique hnormal
  obtain ⟨r, hr8, hsq, hcenter, hcent, hhalf⟩ :=
    IsBinaryHallFactor.exists_large_rotation (pCore_isPGroup.to_subgroup D) hD hnc hlarge
  obtain ⟨R, hR, hsquares, hroots⟩ :=
    cyclic_squares_and_fourth_roots_of_central_product pCore_isPGroup A D hc hg
      r hr8 hsq hcenter hcent hhalf
  let : IsCyclic R := hR
  exact eq_of_isConj_in_four_of_core_power_data hN hrank S hZ E hE hi R
    hsquares hroots z t hzc hz htE hconj

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
