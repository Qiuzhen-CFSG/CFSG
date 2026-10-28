module

public import Theory.GroupTheory.BinaryWeakCorePrimePowerReduction
public import Theory.GroupTheory.ElementaryCommutingOddQuotient

/-!
# Quotient and normalizer reductions for binary centralizer fusion

Write `C = C_G(Q)` and `H = Q C`. If an odd normal quotient of `H` has
a normal two-subgroup containing an elementary eight, then `C` preserves
the rank-three component in the selected two-group. Apply the odd-quotient
component theorem inside `H` to the weak-rank witness `B`, then carry its
path into the ambient group and connect `B` to `A` inside `S`.

An element centralizing `Q` and normalizing `C_S(Q)` also preserves that
component, since it normalizes the two-group `Q C_S(Q)` containing `B`.
These are sufficient conditions, not assertions that an arbitrary odd
element normalizes `C_S(Q)` or that the indicated quotient always exists.

These reductions concern the remaining binary fusion argument following
GLS2, Proposition 22.4 (`refs/KGroup/GLS2/ChapterF.tex`).
-/

namespace Subgroup

/-- Centralizer fusion follows from a normal rank-three two-subgroup in an
odd normal quotient of the commuting product with the centralizer. -/
public theorem elementaryCommutingConnected_conj_of_centralizer_normal_odd_quotient
    {G : Type*} [Group G] [Finite G] (S A Q B : Subgroup G)
    (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B)
    (hAS : A ≤ S) (hQS : Q ≤ S)
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (N : Subgroup ↥(Q ⊔ centralizer (Q : Set G) : Subgroup G)) [N.Normal]
    (hN : Odd (Nat.card N))
    (R D : Subgroup (↥(Q ⊔ centralizer (Q : Set G) : Subgroup G) ⧸ N))
    [R.Normal] (hR : IsPGroup 2 R) [IsElementaryAbelian 2 D]
    (hD : 8 ≤ Nat.card D) (hDR : D ≤ R)
    (c : G) (hc : c ∈ centralizer (Q : Set G)) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom) := by
  let H := Q ⊔ centralizer (Q : Set G)
  have hBH : B ≤ H := hBweak.trans (sup_le_sup_left inf_le_right Q)
  have hBS : B ≤ S := hBweak.trans (sup_le hQS inf_le_left)
  let BH := B.subgroupOf H
  let : IsElementaryAbelian 2 BH := IsElementaryAbelian.subgroupOf hBH
  have hBHcard : 8 ≤ Nat.card BH := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv]
  let cH : H := ⟨c, (le_sup_right : centralizer (Q : Set G) ≤ H) hc⟩
  have hpath := elementaryCommutingConnected_conj_of_normal_odd_quotient
    N BH hN hBHcard R D hR hD hDR cH
  have hambient := hpath.map_injective H.subtype H.subtype_injective
  have hmap : (BH.map (MulAut.conj cH).toMonoidHom).map H.subtype =
      B.map (MulAut.conj c).toMonoidHom := by
    rw [map_map]
    have hhom : H.subtype.comp (MulAut.conj cH).toMonoidHom =
        (MulAut.conj c).toMonoidHom.comp H.subtype := by
      ext x
      rfl
    rw [hhom, ← map_map, map_subgroupOf_eq_of_le hBH]
  rw [map_subgroupOf_eq_of_le hBH, hmap] at hambient
  have hAB := elementaryCommutingConnected_of_le_twoGroup S A B hS hA hB hAS hBS
  exact hAB.trans (hambient.trans (hAB.symm.map (MulAut.conj c)))

/-- The normalizer of the local centralizer, intersected with the ambient
centralizer, preserves the weak-rank component. -/
public theorem elementaryCommutingConnected_conj_of_normalizes_local_centralizer
    {G : Type*} [Group G] [Finite G] (S A Q B : Subgroup G)
    (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B)
    (hAS : A ≤ S) (hQS : Q ≤ S)
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (c : G) (hc : c ∈ centralizer (Q : Set G))
    (hn : c ∈ normalizer ((S ⊓ centralizer (Q : Set G) : Subgroup G) : Set G)) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom) := by
  let R := Q ⊔ (S ⊓ centralizer (Q : Set G))
  have hRS : R ≤ S := sup_le hQS inf_le_left
  have hR : IsPGroup 2 R := hS.to_le hRS
  have hQR : Q.map (MulAut.conj c).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer _ hc)
  have hDn : (S ⊓ centralizer (Q : Set G)).map (MulAut.conj c).toMonoidHom =
      S ⊓ centralizer (Q : Set G) := mem_normalizer_iff_map_conj_eq.mp hn
  have hRn : c ∈ normalizer (R : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change R.map (MulAut.conj c).toMonoidHom = R
    rw [map_sup, hQR, hDn]
  have hAB := elementaryCommutingConnected_of_le_twoGroup S A B hS hA hB hAS
    (hBweak.trans hRS)
  have hBBc := normalizer_le_elementaryCommutingStabilizer_of_le_twoGroup
    R B hR hB hBweak hRn
  exact hAB.trans (hBBc.trans (hAB.symm.map (MulAut.conj c)))

end Subgroup
