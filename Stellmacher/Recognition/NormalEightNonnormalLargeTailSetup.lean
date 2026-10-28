module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Stellmacher.Recognition.NormalFourNonnormalLargeTailStructure
public import Theory.GroupTheory.InvolutionPowerFusion
public import Theory.GroupTheory.PGroup.ExtraspecialCentralProductPowers
public import Theory.GroupTheory.PGroup.LargeBinaryHallRotations

/-!
# Large Hall tails with bounds only on normal elementary subgroups

A large noncyclic Hall tail bounds the actual core preimage's index by two.
Nonnormality of the barred four then makes this index exactly two. Cyclic
squares and commuting fourth roots exclude fusion of the central involution
inside the normal four. Central omega lies in that four by the normal-only
bound, so no bound on arbitrary elementary subgroups is used.

These are the structural and restricted fusion steps of Janko–Thompson,
Math. Z. 113 (1970), §4, Case 1, printed p.392. They adapt
`NormalFourNonnormalLargeTailStructure` and `NormalFourNonnormalLargeTailWeakClosure`.
Weak closure in the whole core and the subsequent ambient transfer argument
are separate from these reductions.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage
open Subgroup NormalFourCentralOmegaTwo
variable {G : Type*} [Group G] [Finite G]

/-- The structural index bound requires only the normal elementary rank bound. -/
public theorem omegaCorePreimage_index_le_two_of_large_noncyclic_tail
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (E : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hA : Nat.card A = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hg : A ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D) :
    (omegaCorePreimage S).index ≤ 2 := by
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic S hno E hunique hnormal
  apply omegaCorePreimage_index_le_two_of_odd_automorphisms hN S hZ
  exact odd_automorphism_card_dvd_three_of_large_hall_central_product
    pCore_isPGroup A D hA hD hn hc hg hlarge

/-- Nonnormality of the barred four excludes index one, independently of the tail. -/
public theorem omegaCorePreimage_index_ne_one
    (S : Sylow 2 G) (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    (omegaCorePreimage S).index ≠ 1 := by
  intro hi
  rw [index_omegaCorePreimage, relIndex_eq_one] at hi
  have heq : (omegaQuotientSylow S : Subgroup (OmegaQuotient S)) =
      pCore 2 (OmegaQuotient S) :=
    le_antisymm hi (pCore_isPGroup.le_sylow_of_normal (omegaQuotientSylow S))
  apply omegaQuotientSylow_not_normal S E hE hunique hnormal
  rw [heq]
  infer_instance

/-- A large noncyclic tail forces the actual core preimage to have index two. -/
public theorem omegaCorePreimage_index_eq_two_of_large_noncyclic_tail
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hA : Nat.card A = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hg : A ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D) :
    (omegaCorePreimage S).index = 2 := by
  have hle := omegaCorePreimage_index_le_two_of_large_noncyclic_tail
    hN S hZ hno E hunique hnormal A D hA hD hn hc hg hlarge
  have hne := omegaCorePreimage_index_ne_one S E hE hunique hnormal
  have hpos := (omegaCorePreimage S).index_ne_zero_of_finite
  omega

/-- Intrinsic cyclic-square and commuting-root data in the actual quotient
core exclude central-involution fusion in the normal four. -/
public theorem eq_of_isConj_in_four_of_core_power_data
    (hN : IsNTwoGroup G)
    (S : Sylow 2 G)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
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
  have hEH : E ≤ H := four_le_omegaCorePreimage hN S hZ E hE hno
  have hzE : z ∈ E := by
    apply omega_one_center_le_normal_four_of_no_normal_eight hno E hE
    refine ⟨⟨z, hzc⟩, subset_closure ?_, rfl⟩
    apply Subtype.ext
    change z ^ (2 ^ 1) = 1
    simpa only [pow_one, hz] using pow_orderOf_eq_one z
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
    (S : Sylow 2 G)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
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
    omegaQuotient_pCore_center_isCyclic S hno E hunique hnormal
  obtain ⟨r, hr8, hsq, hcenter, hcent, hhalf⟩ :=
    IsBinaryHallFactor.exists_large_rotation (pCore_isPGroup.to_subgroup D) hD hnc hlarge
  obtain ⟨R, hR, hsquares, hroots⟩ :=
    cyclic_squares_and_fourth_roots_of_central_product pCore_isPGroup A D hc hg
      r hr8 hsq hcenter hcent hhalf
  let : IsCyclic R := hR
  exact eq_of_isConj_in_four_of_core_power_data hN S hno hZ E hE hi R
    hsquares hroots z t hzc hz htE hconj

end Stellmacher.Recognition.NormalEightNonnormalImage
