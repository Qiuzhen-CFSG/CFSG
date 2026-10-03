module

public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicInsideFusion
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicRotationFusion
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicCosetFusion
public import Theory.GroupTheory.IndexFourInvolutionExtension

/-!
# Assembling the maximal-subgroup involution-class cover

Adjoin an outside involution to the intrinsic rotation product. Index four
for the rotation product makes the join maximal. Fusion inside the rotation
product and fusion in the new involution coset then give the desired cover
by the normal four. The latter coset can be represented by an ambient
conjugate of the central involution.

This assembles the two geometric inputs in Janko–Thompson,
Math. Z. 113 (1970), §4, Case 1, printed p.392. It does not assert either
geometric input as an unconditional fact. In the large-tail specialization,
the actual quotient action discharges inside fusion; only index four and
the outside-coset fusion remain explicit.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage
open Subgroup NormalFourCentralOmegaTwo
variable {G : Type*} [Group G] [Finite G]

/-- Inside and outside fusion for the intrinsic rotation product yield the
maximal-subgroup cover used by Thompson transfer. -/
public theorem involution_cover_of_rotation_fusion
    (S : Sylow 2 G) (W : Subgroup S)
    (hindex : (noncyclicRotationPreimage S).index = 4)
    (hinside : ∀ u : S, u ∈ noncyclicRotationPreimage S → orderOf u = 2 →
      ∃ w : S, w ∈ W ∧ IsConj (u : G) (w : G))
    (z t : S) (hzW : z ∈ W) (ht : orderOf t = 2)
    (hout : t ∉ omegaCorePreimage S) (hconj : IsConj (z : G) (t : G))
    (houtside : ∀ u : S, u ∈ noncyclicRotationPreimage S ⊔ zpowers t →
      u ∉ noncyclicRotationPreimage S → orderOf u = 2 →
      IsConj (u : G) (t : G)) :
    ∃ M : Subgroup S, M.index = 2 ∧ ∀ u : S, u ∈ M → orderOf u = 2 →
      ∃ w : S, w ∈ W ∧ IsConj (u : G) (w : G) := by
  refine ⟨noncyclicRotationPreimage S ⊔ zpowers t, ?_, ?_⟩
  · apply index_sup_zpowers_eq_two_of_index_four _ hindex t
      (by simpa only [ht] using pow_orderOf_eq_one t)
      (fun h => hout (noncyclicRotationPreimage_le S h))
    simp only [normalizer_eq_top, mem_top]
  · intro u hu hu2
    by_cases huK : u ∈ noncyclicRotationPreimage S
    · exact hinside u huK hu2
    · exact ⟨z, hzW, (houtside u hu huK hu2).trans hconj.symm⟩

/-- In the large Hall-tail setup, the quotient action discharges the inside
fusion premise of the maximal-subgroup class cover. -/
public theorem involution_cover_of_large_noncyclic_tail
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (hindex : (noncyclicRotationPreimage S).index = 4)
    (z t : S) (hzW : z ∈ W) (ht : orderOf t = 2)
    (hout : t ∉ omegaCorePreimage S) (hconj : IsConj (z : G) (t : G))
    (houtside : ∀ u : S, u ∈ noncyclicRotationPreimage S ⊔ zpowers t →
      u ∉ noncyclicRotationPreimage S → orderOf u = 2 →
      IsConj (u : G) (t : G)) :
    ∃ M : Subgroup S, M.index = 2 ∧ ∀ u : S, u ∈ M → orderOf u = 2 →
      ∃ w : S, w ∈ W ∧ IsConj (u : G) (w : G) := by
  exact involution_cover_of_rotation_fusion S W hindex
    (exists_isConj_mem_four_of_mem_noncyclicRotationPreimage
      hN S hno hZ W hW hunique hnormal B D hB hD hn hc hg hlarge)
    z t hzW ht hout hconj houtside

/- The complete Case 1 cover.  The central involution is forced into the
chosen normal four by the absence of normal elementary eights; the rotation
index and the outside coset fusion are supplied by the two local geometric
constructions. -/
public theorem involution_cover_of_large_noncyclic_tail_of_core_weak_closure
    [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (hi : (omegaCorePreimage S).index = 2)
    (z t : S) (hzc : z ∈ center S) (hz : orderOf z = 2)
    (hweak : ∀ z u : S, z ∈ center S → orderOf z = 2 →
      u ∈ omegaCorePreimage S → IsConj (z : G) (u : G) → u = z)
    (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    (hconj : IsConj (z : G) (t : G)) :
    ∃ M : Subgroup S, M.index = 2 ∧ ∀ u : S, u ∈ M → orderOf u = 2 →
      ∃ w : S, w ∈ W ∧ IsConj (u : G) (w : G) := by
  have hzW : z ∈ W := by
    apply omega_one_center_le_normal_four_of_no_normal_eight hno W hW
    refine ⟨⟨z, hzc⟩, Subgroup.subset_closure ?_, rfl⟩
    apply Subtype.ext
    change z ^ (2 ^ 1) = 1
    simpa only [pow_one, hz] using pow_orderOf_eq_one z
  have hKindex : (noncyclicRotationPreimage S).index = 4 :=
    noncyclicRotationPreimage_index_eq_four hN S hno hZ W hW hunique hnormal
      B D hB hD hn hc hg hlarge hi
  have hweak' : ∀ u : S, u ∈ omegaCorePreimage S →
      IsConj (z : G) (u : G) → u = z := by
    intro u hu hconju
    exact hweak z u hzc hz hu hconju
  obtain ⟨v, hv, hvout, hvconj, hvoutside⟩ :=
    exists_outside_coset_fusion_of_large_noncyclic_tail hN S hno hZ W hW hunique
      hnormal B D hB hD hn hc hg hlarge hi hKindex z t hzc hz hweak' ht hout hconj
  exact involution_cover_of_large_noncyclic_tail hN S hno hZ W hW hunique hnormal
    B D hB hD hn hc hg hlarge hKindex z v hzW hv hvout hvconj hvoutside

end Stellmacher.Recognition.NormalEightNonnormalImage
