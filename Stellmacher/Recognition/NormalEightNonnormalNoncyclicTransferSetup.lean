module

public import Stellmacher.Recognition.NormalEightNonnormalLargeTailSetup
public import Theory.GroupTheory.CyclicSquareInvolutionCentralizer

/-!
# The elementary centralizer in the large noncyclic transfer case

The large Hall tail supplies cyclic core squares and a fourth root of the
central involution. Transport these along the actual core equivalence.
Weak closure in the index-two core then makes the centralizer of an outside
conjugate elementary abelian. This allows elementary eights and uses no
upper bound on the core order.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, Case 1, printed p.392,
the paragraph beginning “Choose z₁”. The subsequent maximal-subgroup and
involution-class arguments are separate from this elementary-centralizer step.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage
open Subgroup NormalFourCentralOmegaTwo
variable {G : Type*} [Group G] [Finite G]

/-- Core weak closure forces an outside conjugate to have elementary
centralizer. No bound on the size of that elementary subgroup is asserted. -/
public theorem elementary_centralizer_of_large_noncyclic_tail_of_core_weak_closure
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (hi : (omegaCorePreimage S).index = 2)
    (z t : S) (hzc : z ∈ center S) (hz : orderOf z = 2)
    (hweak : ∀ u : S, u ∈ omegaCorePreimage S → IsConj (z : G) (u : G) → u = z)
    (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    (hconj : IsConj (z : G) (t : G)) :
    IsElementaryAbelian 2 (centralizer ({t} : Set S)) := by
  let H := omegaCorePreimage S
  let e := omegaCorePreimageEquiv S
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  obtain ⟨r, hr8, hsq, hcenter, hcent, hhalf⟩ :=
    IsBinaryHallFactor.exists_large_rotation (pCore_isPGroup.to_subgroup D) hD hn hlarge
  obtain ⟨R, hR, hsquares, hroots⟩ :=
    cyclic_squares_and_fourth_roots_of_central_product pCore_isPGroup B D hc hg
      r hr8 hsq hcenter hcent hhalf
  let : IsCyclic R := hR
  have hWH : W ≤ H := four_le_omegaCorePreimage hN S hZ W hW hno
  have hzW : z ∈ W := by
    apply omega_one_center_le_normal_four_of_no_normal_eight hno W hW
    refine ⟨⟨z, hzc⟩, subset_closure ?_, rfl⟩
    apply Subtype.ext
    change z ^ (2 ^ 1) = 1
    simpa only [pow_one, hz] using pow_orderOf_eq_one z
  let zH : H := ⟨z, hWH hzW⟩
  let F := (W.subgroupOf H).map e.toMonoidHom
  let : IsElementaryAbelian 2 (W.subgroupOf H) := IsElementaryAbelian.subgroupOf hWH
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map _
  let : F.Normal := (inferInstance : (W.subgroupOf H).Normal).map _ e.surjective
  have hF : Nat.card F = 4 := by
    rw [card_map_of_injective e.injective]
    exact (Nat.card_congr (subgroupOfEquivOfLe hWH).toEquiv).trans hW
  have hzC : e zH ∈ center (pCore 2 (OmegaQuotient S)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨u, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (mem_center_iff.mp hzc (u : S)))
  have hzO : orderOf (e zH) = 2 := by
    rw [e.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hz
  have hzF : e zH ∈ F := mem_map_of_mem e.toMonoidHom hzW
  obtain ⟨x, hx, -⟩ := hroots F inferInstance inferInstance hF
    (e zH) (e zH) hzC hzO hzF
  let R' := R.comap e.toMonoidHom
  let : IsCyclic R' := isCyclic_of_injective (e.toMonoidHom.subgroupComap R) (by
    intro a b h
    exact Subtype.ext (e.injective (congrArg Subtype.val h)))
  have hsquares' (u : H) : u ^ 2 ∈ R' := by
    change e (u ^ 2) ∈ R
    rw [map_pow]
    exact hsquares (e u)
  have hzR : zH ∈ R' := by
    change e zH ∈ R
    rw [← hx, show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    exact hsquares (x ^ 2)
  exact S.elementary_centralizer_of_index_two_of_cyclic_squares H hi R' hsquares'
    zH hzR ((Subgroup.orderOf_coe zH).symm.trans hz) hzc hweak t
    (by simpa only [ht] using pow_orderOf_eq_one t) hout hconj

end Stellmacher.Recognition.NormalEightNonnormalImage
