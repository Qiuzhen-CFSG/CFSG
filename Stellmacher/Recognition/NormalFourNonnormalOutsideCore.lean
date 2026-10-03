module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Theory.GroupTheory.CentralSquareFusion
public import Stellmacher.Recognition.NormalFourNonnormalCoreInvolutionFusion
public import Theory.GroupTheory.PGroup.OutsideInvolutionSquare

/-!
# The outside-core fusion obstruction from a central square

If the central involution is a square in the Sylow center, all of its ambient
conjugates in the Sylow subgroup belong to the actual quotient-core preimage.
A transported square root centralizes the original involution, hence lies in
its omega normalizer. Its square belongs to the preimage of the quotient core,
whose relative Sylow index is two.

The actual order-sixteen core has cyclic center of order four and a second
core-normal elementary four, since the quotient has no normal four. Transport
these subgroups to the Sylow core preimage. The intrinsic outside-involution
calculation then supplies a square root in the Sylow center, completing the
outside-core exclusion. In particular the requested centralizing-four
conclusion follows from the contradiction in the outside case.

This is an alternative argument for the penultimate paragraph of
Janko–Thompson, Math. Z. 113 (1970), Lemma 4.1, printed p.393; see
`normal-four-case-split.md` beside the saved source PDF. The actual normal
four-subgroups, their conjugation action and the cyclic core center are used;
no centralizer structure is inferred merely from orders.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A central involution with a central square root cannot fuse outside the
actual quotient-core preimage when that core has relative Sylow index two. -/
public theorem mem_omegaCorePreimage_of_isConj_of_central_square
    (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hindex : (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (r : S) (hr : r ∈ center S) (hrz : r ^ 2 = z)
    (t : S) (hconj : IsConj (z : G) (t : G)) : t ∈ omegaCorePreimage S := by
  have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hzZ : (z : G) ∈ centralOmega S := by
    apply mem_map_of_mem
    refine ⟨⟨z, hzc⟩, subset_closure ?_, rfl⟩
    exact (show (⟨z, hzc⟩ : center S) ^ (2 ^ 1) = 1 from
      Subtype.ext (by simpa using hz2))
  have hline : zpowers (z : G) = centralOmega S := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hzZ)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, card_centralOmega, hZ]
  obtain ⟨x, hxt, hxz, hx⟩ :=
    S.exists_commuting_square_root_of_isConj z hz hzc r hr hrz t hconj.symm
  have hxN : x ∈ omegaNormalizer S := by
    change x ∈ normalizer (centralOmega S : Set G)
    rw [← hline]
    apply Subgroup.centralizer_le_normalizer
    rintro y ⟨n, rfl⟩
    exact (hxz.zpow_right n).symm
  let N := omegaNormalizer S
  let q := QuotientGroup.mk' (pPrimeCore 2 N)
  let K := (pCore 2 (OmegaQuotient S)).comap q
  let P := S.subtype (sylow_le_omegaNormalizer S)
  have hi : K.relIndex P = 2 := by
    change ((pCore 2 (OmegaQuotient S)).comap q).relIndex P = 2
    rw [relIndex_comap]
    simpa only [omegaQuotientSylow_coe] using hindex
  have hxK : (⟨x, hxN⟩ : N) ^ 2 ∈ K :=
    P.sq_mem_normal_of_relIndex_two K hi ⟨x, hxN⟩ ((Subgroup.orderOf_coe _).symm.trans hx)
  have he : (⟨x, hxN⟩ : N) ^ 2 = ⟨(t : G), sylow_le_omegaNormalizer S t.property⟩ :=
    Subtype.ext hxt
  rw [he] at hxK
  change omegaQuotientHom S t ∈ pCore 2 (OmegaQuotient S)
  rw [omegaQuotientHom_apply]
  exact hxK

/-- The genuine core preimage inherits the quotient core's symplectic type. -/
public theorem omegaCorePreimage_symplectic
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (E : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    IsBinarySymplecticType (omegaCorePreimage S) :=
  (omegaQuotient_pCore_symplectic hrank S E hunique hnormal).of_mulEquiv
    (omegaCorePreimageEquiv S).symm

/-- The genuine core preimage has cyclic center. -/
public theorem omegaCorePreimage_center_isCyclic
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (E : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    IsCyclic (center (omegaCorePreimage S)) :=
  (centerCongr (omegaCorePreimageEquiv S)).isCyclic.mpr
    (omegaQuotient_pCore_center_isCyclic hrank S E hunique hnormal)

/-- The genuine core preimage is not a pure Hall factor. -/
public theorem omegaCorePreimage_not_hall (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hnormal : ¬ (fourImage S E).Normal) :
    ¬ IsBinaryHallFactor (omegaCorePreimage S) := by
  intro h
  exact omegaQuotient_pCore_not_hall hN hrank S hZ E hE hnormal
    (h.of_mulEquiv (omegaCorePreimageEquiv S))

private theorem core_distinct_four
    (S : Sylow 2 G) (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) (hEH : E ≤ omegaCorePreimage S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal) :
    ∃ F : Subgroup S, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
      F ≤ omegaCorePreimage S ∧ omegaCorePreimage S ≤ normalizer (F : Set S) ∧ F ≠ E := by
  let H := omegaCorePreimage S
  let K := pCore 2 (OmegaQuotient S)
  let e := omegaCorePreimageEquiv S
  let U := E.subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hEH
  let V := U.map e.toMonoidHom
  let : V.Normal := e.normal_map_iff.mpr inferInstance
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hU : Nat.card U = 4 := (Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv).trans hE
  have hV : Nat.card V = 4 := (card_map_of_injective e.injective).trans hU
  obtain ⟨W, hWn, hWe, hW, hWV⟩ := exists_distinct_normal_four_of_no_ambient_normal_four K
    (omegaQuotient_no_normal_four S E hunique hnormal) V hV
  let : W.Normal := hWn
  let : IsElementaryAbelian 2 W := hWe
  let A := W.map e.symm.toMonoidHom
  let : A.Normal := e.symm.normal_map_iff.mpr hWn
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let F := A.map H.subtype
  have hF : Nat.card F = 4 := by
    rw [card_map_of_injective H.subtype_injective, card_map_of_injective e.symm.injective, hW]
  have hFH : F ≤ H := map_subtype_le A
  have hAF : F.subgroupOf H = A := by
    exact comap_map_eq_self_of_injective H.subtype_injective A
  have hFn : (F.subgroupOf H).Normal := hAF.symm ▸ inferInstance
  refine ⟨F, IsElementaryAbelian.map _, hF, hFH,
    (normal_subgroupOf_iff_le_normalizer hFH).mp hFn, ?_⟩
  intro hFE
  have hAU : A = U := hAF.symm.trans (congrArg (fun B : Subgroup S => B.subgroupOf H) hFE)
  apply hWV
  change W = U.map e.toMonoidHom
  rw [← hAU]
  change W = (W.map e.symm.toMonoidHom).map e.toMonoidHom
  ext w
  simp only [mem_map_equiv, MulEquiv.symm_symm, e.apply_symm_apply]

/-- Every Sylow involution conjugate to the central involution lies in the
actual core preimage when that core has order sixteen and index two. -/
public theorem mem_omegaCorePreimage_of_isConj_central_involution
    (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16)
    (hindex : (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2)
    (z : E) (hz : orderOf (z : S) = 2) (hzc : (z : S) ∈ center S)
    (t : S) (ht : orderOf t = 2) (hconj : IsConj ((z : S) : G) (t : G)) :
    t ∈ omegaCorePreimage S := by
  by_contra htH
  let H := omegaCorePreimage S
  have hEH : E ≤ H := four_le_omegaCorePreimage hN hrank S hZ E hE
  obtain ⟨F, hFe, hF, hFH, hFn, hFE⟩ := core_distinct_four S E hE hEH hunique hnormal
  let : IsElementaryAbelian 2 F := hFe
  let : IsCyclic (center H) := omegaCorePreimage_center_isCyclic hrank S E hunique hnormal
  have hcenter : Nat.card (center H) = 4 :=
    (Nat.card_congr (centerCongr (omegaCorePreimageEquiv S)).toEquiv).trans
      (omegaQuotient_pCore_dihedral_center_four hN hrank S hZ E hE hunique hnormal hcore).2.1
  obtain ⟨r, hrc, hrz⟩ := exists_central_square_of_order_sixteen_core
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) H E F
    ((card_omegaCorePreimage S).trans hcore) hcenter ((index_omegaCorePreimage S).trans hindex)
    hE hF hEH hFH hFn hFE hunique z t z.property hz hzc
    (by simpa only [ht] using pow_orderOf_eq_one t) htH
  exact htH (mem_omegaCorePreimage_of_isConj_of_central_square S hZ hindex z hz hzc r hrc hrz t hconj)

/-- The outside-conjugate configuration is impossible; in particular it gives
the centralizing-four conclusion needed by terminal fusion. -/
public theorem exists_four_centralized_of_outside_core_isConj
    (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16)
    (hindex : (pCore 2 (OmegaQuotient S)).relIndex (omegaQuotientSylow S) = 2)
    (z : E) (hz : orderOf (z : S) = 2) (hzc : (z : S) ∈ center S)
    (t : S) (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    (hconj : IsConj ((z : S) : G) (t : G)) :
    ∃ F : Subgroup S, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
      F ≤ omegaCorePreimage S ∧ t ∈ centralizer (F : Set S) := by
  exact (hout (mem_omegaCorePreimage_of_isConj_central_involution hN hrank S hZ E hE
    hunique hnormal hcore hindex z hz hzc t ht hconj)).elim

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
