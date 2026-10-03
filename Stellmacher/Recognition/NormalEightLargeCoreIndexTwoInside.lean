module

public import Stellmacher.Recognition.NormalEightLargeCoreIndexTwoSetup
public import Stellmacher.Recognition.NormalEightLargeCoreIndexTwoTransport
public import Stellmacher.Recognition.NormalEightOrder64FusedFour
public import Theory.GroupTheory.NormalFourFusion
public import Theory.GroupTheory.PGroup.FusedFourCharacteristic

/-!
# Inside-core fusion in the normal-only index-two case

A distinct central-involution conjugate in the unique normal four fuses all
three of its involutions. Thus inside-core nonfusion reduces to two inputs:
transporting an inside-core conjugate into that four, and excluding fusion
of the four when the Sylow has order sixty-four.

The conditional assembly keeps those inputs explicit, and the final theorem
discharges both using the transport and order-sixty-four exclusion modules.
The first is the Sylow centralizer argument, and the second specializes
the recognition consequence of
1.3–1.4 in Janko–Thompson, Math. Z. 113 (1970), printed pp.386 and 389,
the paragraph beginning “Suppose |T:H|=2”. Neither input is replaced by
a bound on arbitrary elementary subgroups.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- A distinct conjugate of a central involution in the normal four fuses
its three involutions using only the normal-elementary bound. -/
public theorem normal_four_fused_of_distinct_central_conjugate
    (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (z u : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (huW : u ∈ W) (huz : u ≠ z) (hzu : IsConj (z : G) (u : G)) :
    ∀ x y : W, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G) := by
  have hzW : z ∈ W := omega_one_center_le_normal_four_of_no_normal_eight hno W hW
    ⟨⟨z, hzc⟩, subset_closure (by
      apply Subtype.ext
      change z ^ (2 ^ 1) = 1
      simpa only [pow_one, hz] using pow_orderOf_eq_one z), rfl⟩
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  have hu1 : u ≠ 1 := by
    intro h
    have hzG : (z : G) = 1 := isConj_one_left.mp (by simpa only [h, coe_one] using hzu)
    exact hz1 (Subtype.ext hzG)
  exact normal_four_fusion_of_central_isConj W hW
    (four_not_le_center_of_card_omega_one_center_eq_two hZ W hW)
    ⟨z, hzW⟩ hzc (fun h => hz1 (congrArg Subtype.val h))
    (S : Subgroup G).subtype ⟨u, huW⟩
    (fun h => hu1 (congrArg Subtype.val h))
    (fun h => huz (congrArg Subtype.val h)) hzu

/-- The two source inputs suffice for exactly the inside-core premise of
the checked index-two assembly. -/
public theorem large_core_index_two_inside_fusion_of_transport_and_recognition
    (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 2)
    (htransport : ∀ z t : S, orderOf z = 2 → z ∈ center S →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t ≠ z →
      ∃ u : S, u ∈ W ∧ u ≠ z ∧ IsConj (t : G) (u : G))
    (hrecognition :
      (∀ x y : W, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) →
        Nat.card S ≠ 64) :
    ∀ z t : S, orderOf z = 2 → z ∈ center S →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z := by
  intro z t hz hzc htH hzt
  by_contra hne
  obtain ⟨u, huW, huz, htu⟩ := htransport z t hz hzc htH hzt hne
  exact hrecognition
    (normal_four_fused_of_distinct_central_conjugate S hZ hno W hW
      z u hz hzc huW huz (hzt.trans htu))
    (card_sylow_of_large_core_index_two S hH hindex)

/-- The central involution has no distinct ambient conjugate inside the
extraspecial core of index two. This uses only the normal-elementary bound
and applies to both extraspecial types of order thirty-two. -/
public theorem large_core_index_two_inside_fusion
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 2) :
    ∀ z t : S, orderOf z = 2 → z ∈ center S →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z := by
  apply large_core_index_two_inside_fusion_of_transport_and_recognition
    S hZ hno W hW hH hindex
    (large_core_index_two_transport hN S hZ hno W hW hunique hH hindex)
  intro hfused hS
  exact NormalEightOrder64FusedFour.false_of_fused_normal_four
    S hS hZ hno W hW hunique hfused

end Stellmacher.Recognition.NormalEightNonnormalImage
