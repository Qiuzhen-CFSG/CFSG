module

public import Stellmacher.Recognition.NormalEightNonnormalLargeTailSetup
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicWeakClosure
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicTransfer
public import Stellmacher.Recognition.SimpleInvolutionFusion

/-!
# Fusion reductions for the noncyclic Hall tail

A large noncyclic Hall tail prevents distinct fusion of the central Sylow
involution inside the normal four. Thus the strict tail bound follows once
such fusion into the four is established. Alternatively, weak closure in
the entire core preimage puts a distinct conjugate outside that preimage,
providing the involution needed for the transfer argument.

These implications keep the normal-only elementary bound explicit. They do
not assert that an arbitrary elementary eight is impossible. The remaining
core weak-closure and transfer steps are those of Janko–Thompson,
Math. Z. 113 (1970), §4, Case 1, printed pp.392–393.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- The strict noncyclic tail bound follows from distinct fusion into the
normal four. The structural index bound is proved rather than assumed. -/
public theorem omegaQuotient_noncyclicHallTail_card_lt_sixteen_of_four_fusion
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤)
    (hfusion : ∃ z t : S, z ∈ center S ∧ orderOf z = 2 ∧ t ∈ W ∧
      t ≠ z ∧ IsConj (z : G) (t : G)) : Nat.card D < 16 := by
  by_contra! hlarge
  have hi := omegaCorePreimage_index_le_two_of_large_noncyclic_tail
    hN S hZ hno W hunique hnormal B D hB hD hn hc hg hlarge
  obtain ⟨z, t, hzC, hz, htW, hne, hconj⟩ := hfusion
  exact hne (eq_of_isConj_in_four_of_large_noncyclic_tail
    hN S hno hZ W hW hunique hnormal hi B D hD hn hc hg hlarge
    z t hzC hz htW hconj)

/-- Weak closure in the core preimage forces a distinct conjugate outside
it. This supplies the outside involution for the source's transfer step. -/
public theorem exists_isConj_outside_omegaCorePreimage_of_weak_closure
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hweak : ∀ z t : S, z ∈ center S → orderOf z = 2 →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z) :
    ∃ z t : S, z ∈ center S ∧ orderOf z = 2 ∧ orderOf t = 2 ∧
      t ∉ omegaCorePreimage S ∧ t ≠ z ∧ IsConj (z : G) (t : G) := by
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let z : S := (w : center S)
  have hz : orderOf z = 2 := (orderOf_coe (w : center S)).trans
    ((orderOf_coe w).trans hw)
  have hzC : z ∈ center S := (w : center S).property
  obtain ⟨t, hne, ht⟩ := exists_distinct_isConj_in_sylow hns S z hz
  have htorder : orderOf t = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp ht
    have heq : (MulAut.conj g) (z : G) = (t : G) := hg
    rw [← orderOf_coe, ← heq, MulEquiv.orderOf_eq, orderOf_coe, hz]
  exact ⟨z, t, hzC, hz, htorder, fun h => hne (hweak z t hzC hz h ht), hne, ht⟩

/-- A large noncyclic Hall tail is impossible under the normal-only rank
bound.  The index-two core weak closure and Thompson-transfer contradiction
discharge the fusion premise needed by the structural reduction. -/
public theorem omegaQuotient_noncyclicHallTail_card_lt_sixteen
    [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (_hA : 8 ≤ Nat.card A)
    (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧
      8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (_hwidth : ∀ B' D' : Subgroup (pCore 2 (OmegaQuotient S)),
      B'.Normal → D'.Normal → IsExtraspecial 2 B' → IsBinaryHallFactor D' →
      D' ≤ centralizer (B' : Set (pCore 2 (OmegaQuotient S))) →
      B' ⊔ D' = ⊤ → Nat.card B' = 8)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) :
    Nat.card D < 16 := by
  by_contra hsmall
  have hlarge : 16 ≤ Nat.card D := Nat.le_of_not_gt hsmall
  have hi : (omegaCorePreimage S).index = 2 :=
    omegaCorePreimage_index_eq_two_of_large_noncyclic_tail
      hN S hZ hno W hW hunique hnormal B D hB hD hn hc hg hlarge
  have hweak := omegaCorePreimage_weakly_closed_of_large_noncyclic_tail
    hns hN S hZ hno W hW hunique hnormal B D hB hD hn hc hg hlarge _hwidth
  obtain ⟨z, t, hzc, hz, ht, hout, htne, hconj⟩ :=
    exists_isConj_outside_omegaCorePreimage_of_weak_closure
      hns S hZ hweak
  exact (large_noncyclic_tail_false_of_core_weak_closure
    hns hN S A _hA _hnonab hZ hno W hW hunique hnormal B D hB hD hn hc hg
    hlarge _hwidth hi hweak z t hzc hz ht hout htne hconj).elim

end Stellmacher.Recognition.NormalEightNonnormalImage
