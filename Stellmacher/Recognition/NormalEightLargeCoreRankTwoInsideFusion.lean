module

public import Stellmacher.Recognition.NormalEightLargeCoreHigherIndexRankTwo
public import Stellmacher.Recognition.NormalEightLargeCoreIndexTwoInside
public import Stellmacher.Recognition.NormalEightMinusCoreLocalAction
public import Stellmacher.Recognition.NormalEightOrder128FusedFour

/-!
# Inside-core fusion from the noncentral involution orbit

An orbit containing all noncentral core involutions transports a putative
conjugate of the central Sylow involution into the normal four. Fusion of
that four then supplies the recognition obstruction. This transport uses
only the normal elementary bound, not an elementary-rank bound on the Sylow.

The actual local action supplies a cyclic core quotient of order four and
the noncentral involution orbit. The independent order-128 recognition
obstruction excludes fusion of the normal four. Transferring the intrinsic
core rank to its Sylow preimage completes inside-core weak closure.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389, the ten
noncentral involutions and the subsequent appeal to results 1.3–1.5.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- A single noncentral core orbit turns a distinct fused core involution
into fusion of the unique normal four. No ambient rank bound is used. -/
public theorem large_core_four_fused_of_core_orbit
    (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hWH : W ≤ omegaCorePreimage S)
    (z t : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (ht : orderOf t = 2) (htH : t ∈ omegaCorePreimage S)
    (htz : t ≠ z) (hzt : IsConj (z : G) (t : G))
    (horbit : ∀ x y : S, x ∈ omegaCorePreimage S → orderOf x = 2 → x ≠ z →
      y ∈ omegaCorePreimage S → orderOf y = 2 → y ≠ z →
      IsConj (x : G) (y : G)) :
    ∀ x y : W, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G) := by
  obtain ⟨u, huW, huc⟩ := SetLike.not_le_iff_exists.mp
    (four_not_le_center_of_card_omega_one_center_eq_two hZ W hW)
  have hu1 : u ≠ 1 := fun h => huc (h ▸ (center S).one_mem)
  have huz : u ≠ z := fun h => huc (h ▸ hzc)
  have hu : orderOf u = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian u huW) hu1
  exact normal_four_fused_of_distinct_central_conjugate S hZ hno W hW z u hz hzc
    huW huz (hzt.trans (horbit t u htH ht htz (hWH huW) hu huz))

/-- The local action supplies the orbit and core index; recognition excludes
the resulting fused four at Sylow order 128. These inputs imply exactly the
inside-core weak closure needed for the outside-conjugate theorem. -/
public theorem large_core_rank_two_inside_fusion_of_orbit_and_recognition
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 4)
    (horbit : ∀ z : S, orderOf z = 2 → z ∈ center S →
      ∀ x y : S, x ∈ omegaCorePreimage S → orderOf x = 2 → x ≠ z →
        y ∈ omegaCorePreimage S → orderOf y = 2 → y ≠ z →
        IsConj (x : G) (y : G))
    (hrecognition : Nat.card S = 128 →
      (∀ x y : W, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) → False) :
    ∀ z t : S, orderOf z = 2 → z ∈ center S → orderOf t = 2 →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z := by
  have hS : Nat.card S = 128 := by
    have hc := (omegaCorePreimage S).card_mul_index
    rw [card_omegaCorePreimage, hH, hindex] at hc
    exact hc.symm
  intro z t hz hzc ht htH hzt
  by_contra htz
  exact hrecognition hS (large_core_four_fused_of_core_orbit S hZ hno W hW
    (four_le_omegaCorePreimage hN S hZ W hW hno) z t hz hzc ht htH htz hzt
    (horbit z hz hzc))

/-- The central Sylow involution is weakly closed among core involutions.
The rank bound is intrinsic to the quotient core; arbitrary elementary
subgroups of the Sylow subgroup are not bounded. -/
public theorem large_core_rank_two_inside_fusion
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : 4 ≤ (omegaCorePreimage S).index)
    (hcoreRank : ∀ E : Subgroup (pCore 2 (OmegaQuotient S)),
      IsElementaryAbelian 2 E → Nat.card E < 8) :
    ∀ z t : S, orderOf z = 2 → z ∈ center S → orderOf t = 2 →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z := by
  obtain ⟨hi, hcyclic⟩ :=
    minus_core_index_four_and_isCyclic hN S hZ hH hcoreRank hindex
  let : IsCyclic (S ⧸ omegaCorePreimage S) := hcyclic
  let : IsExtraspecial 2 (omegaCorePreimage S) :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  apply large_core_rank_two_inside_fusion_of_orbit_and_recognition
    hN S hZ hno W hW hH hi
    (minus_core_noncentral_involutions_isConj hN S hZ hH hcoreRank hindex)
  intro hS hfused
  exact NormalEightOrder128FusedFour.false_of_fused_normal_four S hS hZ hno W hW
    hunique (omegaCorePreimage S) ((card_omegaCorePreimage S).trans hH)
    (four_le_omegaCorePreimage hN S hZ W hW hno) hi
    (fun E hE => @omegaCorePreimage_elementary_card_lt_eight G _ _ S hcoreRank E hE)
    hfused

end Stellmacher.Recognition.NormalEightNonnormalImage
