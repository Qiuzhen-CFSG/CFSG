module

public import Stellmacher.Recognition.NormalEightNonnormalLargeTailSetup
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicTransferSetup
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicClassSeparation
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicClassCover
public import Theory.GroupTheory.InvolutionTransfer

/-!
# Transfer after core weak closure

An index-two subgroup whose involutions are fused into the normal four
forces every Sylow involution to fuse into that four, by Thompson transfer.
A core involution distinct from the central involution cannot fuse to the
central involution by core weak closure. Excluding its fusion to the other
two members of the four therefore gives the ambient contradiction.

This isolates the final assembly of Janko–Thompson, Math. Z. 113 (1970),
§4, Case 1, printed pp.392–393. The maximal-subgroup class cover and the
core involution avoiding the other two classes are the two geometric inputs.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage
open Subgroup NormalFourCentralOmegaTwo
variable {G : Type*} [Group G] [Finite G]

/-- Thompson transfer completes the contradiction from a maximal-subgroup
class cover and a core involution avoiding the noncentral classes of the four. -/
public theorem false_of_core_weak_closure_of_involution_cover [IsSimpleGroup G]
    (S : Sylow 2 G) (W : Subgroup S) (hW : Nat.card W = 4)
    (z : S)
    (hweak : ∀ u : S, u ∈ omegaCorePreimage S → IsConj (z : G) (u : G) → u = z)
    (hcover : ∃ M : Subgroup S, M.index = 2 ∧ ∀ u : S, u ∈ M → orderOf u = 2 →
      ∃ w : S, w ∈ W ∧ IsConj (u : G) (w : G))
    (hseparate : ∃ x : S, x ∈ omegaCorePreimage S ∧ orderOf x = 2 ∧ x ≠ z ∧
      ∀ w : S, w ∈ W → w ≠ z → ¬ IsConj (x : G) (w : G)) : False := by
  have hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2 := by
    intro K hK hi
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K hK with hb | ht
    · have hbound : 4 ≤ Nat.card G := hW ▸
        W.card_le_card_group.trans (S : Subgroup G).card_le_card_group
      rw [hb, index_bot] at hi
      omega
    · simp [ht] at hi
  obtain ⟨M, hM, hclasses⟩ := hcover
  obtain ⟨x, hxH, hx, hne, hsep⟩ := hseparate
  obtain ⟨u, hxu, huM⟩ := S.exists_isConj_mem_of_index_two hno M hM x hx
  have hu : orderOf u = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hxu
    have he : (MulAut.conj g) (x : G) = u := hg
    rw [← Subgroup.orderOf_coe, ← he, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hx]
  obtain ⟨w, hwW, huw⟩ := hclasses u huM hu
  have hxw := hxu.trans huw
  by_cases hwz : w = z
  · rw [hwz] at hxw
    exact hne (hweak x hxH hxw.symm)
  · exact hsep w hwW hwz hxw

/-! The complete large noncyclic Hall-tail transfer contradiction.  The
maximal-subgroup class cover and the separated core involution are supplied by
the two independent geometric constructions, while the central involution's
weak closure is used only in the transfer step. -/
public theorem large_noncyclic_tail_false_of_core_weak_closure
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
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (_hwidth : ∀ B' D' : Subgroup (pCore 2 (OmegaQuotient S)),
      B'.Normal → D'.Normal → IsExtraspecial 2 B' → IsBinaryHallFactor D' →
      D' ≤ centralizer (B' : Set (pCore 2 (OmegaQuotient S))) →
      B' ⊔ D' = ⊤ → Nat.card B' = 8)
    (hi : (omegaCorePreimage S).index = 2)
    (hweak : ∀ z t : S, z ∈ center S → orderOf z = 2 →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z)
    (z t : S) (hzc : z ∈ center S) (hz : orderOf z = 2)
    (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    (_htne : t ≠ z) (hconj : IsConj (z : G) (t : G)) : False := by
  have hweak' : ∀ u : S, u ∈ omegaCorePreimage S →
      IsConj (z : G) (u : G) → u = z := by
    intro u hu hconju
    exact hweak z u hzc hz hu hconju
  have hcover := involution_cover_of_large_noncyclic_tail_of_core_weak_closure
    hns hN S hno hZ W hW hunique hnormal B D hB hD hn hc hg hlarge hi
    z t hzc hz hweak ht hout hconj
  have hseparate := exists_core_involution_separated_of_large_noncyclic_tail
    hN S hno hZ W hW hunique hnormal B D hB hD hn hc hg hlarge hi z hzc hz
  exact false_of_core_weak_closure_of_involution_cover S W hW z hweak' hcover
    hseparate

end Stellmacher.Recognition.NormalEightNonnormalImage
