module

public import Stellmacher.Recognition.NormalEightNonnormalCyclicWeakClosure
public import Theory.GroupTheory.CyclicCoreInvolutionCentralizer
public import Theory.GroupTheory.SaturatedCentralizer

/-!
# A saturated elementary-eight centralizer in the large cyclic-tail case

Choose a distinct conjugate of the central Sylow involution and saturate
its centralizer inside the ambient centralizer of the original involution.
Core weak closure keeps the chosen conjugate outside the core preimage.
The core has index two, cyclic center, and central squares, so square fusion
makes the chosen centralizer elementary.

The extraspecial-eight/cyclic presentation puts the core center at index
four. Its elementary subgroups have order at most four, and the outside
centralizer therefore has order at most eight. The given elementary eight
in the Sylow subgroup excludes a centralizer of order four and gives the
exact order. Neither intrinsic width nor a global elementary-rank bound is
needed. Saturation is in C_G(z) ∩ C_G(t), as required by the source.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, Case 2, printed p.393;
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- A large cyclic tail supplies an outside conjugate whose Sylow centralizer
is elementary of order eight and maximal among two-subgroups of the
simultaneous ambient centralizer. -/
public theorem exists_saturated_elementary_eight_centralizer_of_large_cyclic_tail
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] [IsCyclic D] (hB : Nat.card B = 8)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hgen : B ⊔ D = ⊤) (hlarge : 8 ≤ Nat.card D)
    (z : S) (hzC : z ∈ center S) (hz : orderOf z = 2) :
    ∃ t : S, t ∉ omegaCorePreimage S ∧ IsConj (z : G) (t : G) ∧
      IsElementaryAbelian 2 (centralizer ({t} : Set S)) ∧
      Nat.card (centralizer ({t} : Set S)) = 8 ∧
      ∀ V : Subgroup G, IsPGroup 2 V →
        (centralizer ({t} : Set S)).map (S : Subgroup G).subtype ≤ V →
        V ≤ centralizer ({(z : G), (t : G)} : Set G) →
        V = (centralizer ({t} : Set S)).map (S : Subgroup G).subtype := by
  let R := omegaCorePreimage S
  have hzR : z ∈ R := central_involution_mem_omegaCorePreimage hN S hZ W hW hno z hzC hz
  have hweak := omegaCorePreimage_weakly_closed_of_large_cyclic_tail
    hN S hZ W hW hno hunique hnormal B D hB hc hgen hlarge z
  obtain ⟨x, hx, hconj⟩ := exists_conjugate_outside_core_of_large_cyclic_tail
    hns hN S hZ W hW hno hunique hnormal B D hB hc hgen hlarge z hzC hz
  obtain ⟨t, htz, hzt, hmax⟩ :=
    S.exists_distinct_conjugate_with_saturated_common_centralizer z hzC x
      (fun h => hx (h ▸ hzR)) hconj
  have htR : t ∉ R := fun ht => htz (hweak t hzC hz ht hzt)
  have hD : D ≠ ⊥ := by intro h; rw [h, card_bot] at hlarge; omega
  obtain ⟨hcyc, hcardZ⟩ := omegaCorePreimage_center_cyclic_tail
    S hno W hunique hnormal B D hD hc hgen
  let : IsCyclic (center R) := hcyc
  have hi : R.index = 2 := omegaCorePreimage_index_two_of_cyclic_tail
    hN S hZ W hW hunique hnormal B D hB hgen
  have hsq (r : R) : r ^ 2 ∈ center R := by
    apply mem_center_iff.mpr
    intro s
    apply (omegaCorePreimageEquiv S).injective
    rw [map_mul, map_mul, map_pow]
    exact mem_center_iff.mp
      (square_mem_center_of_extraspecial_cyclic_product B D hc hgen
        (omegaCorePreimageEquiv S r)) (omegaCorePreimageEquiv S s)
  let : IsElementaryAbelian 2 (centralizer ({t} : Set S)) :=
    S.elementary_centralizer_of_cyclic_core R hi hsq z hzC hz hzR
      (fun u hu huconj => hweak u hzC hz hu huconj) t htR hzt
  have hRcard : Nat.card R = 4 * Nat.card (center R) := by
    have hS := card_sylow_eq_eight_mul_cyclic_tail
      hN S hZ W hW hno hunique hnormal B D hB hD hc hgen
    have hR := R.card_mul_index
    rw [hi, hS] at hR
    change Nat.card (center R) = Nat.card D at hcardZ
    omega
  refine ⟨t, htR, hzt, inferInstance, ?_, hmax⟩
  exact S.card_centralizer_eq_eight_of_elementary_of_index_two_core A hA R hi
    (fun F hF => by
      let : IsElementaryAbelian 2 F := hF
      exact Subgroup.elementary_card_le_four_of_cyclic_center_index_four hRcard F)
    z hzC hz hzR t htR

end Stellmacher.Recognition.NormalEightNonnormalImage
