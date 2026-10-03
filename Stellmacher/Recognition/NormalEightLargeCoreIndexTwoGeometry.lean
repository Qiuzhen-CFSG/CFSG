module

public import Stellmacher.Recognition.NormalEightLargeCoreIndexTwoSetup
public import Theory.GroupTheory.SaturatedCentralizer
public import Theory.GroupTheory.PGroup.ExtraspecialIndexTwoCrossingNormalizer

/-!
# Saturated elementary centralizers in the index-two large-core case

Choose an outside conjugate of a central Sylow involution and then conjugate
inside the centralizer of the original involution. This makes the Sylow
centralizer maximal among two-subgroups of the simultaneous centralizer.
Inside-core nonfusion keeps the new conjugate outside the extraspecial core.
The local index-two geometry then makes its centralizer elementary of order
eight, with core intersection equal to the unique normal four.

Every elementary eight crossing the core also meets it in that four. The
extraspecial extension gives a normalizer of order at least thirty-two for
both contained and crossing eights; the absence of normal elementary eights
gives the matching upper bound. Thus every elementary eight has normalizer
of order thirty-two.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389, the
index-two paragraph; `refs/original/n-group-global/odd-core-rank-two-source/`.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- Inside-core nonfusion gives an elementary eight saturated in the
simultaneous centralizer of a central Sylow involution and an outside conjugate.
The normal-only restriction suffices; arbitrary elementary eights are allowed. -/
public theorem large_core_index_two_saturated_elementary_centralizer
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 2)
    (hinside : ∀ z t : S, orderOf z = 2 → z ∈ center S →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z) :
    ∃ z t : S, orderOf z = 2 ∧ z ∈ center S ∧
      orderOf t = 2 ∧ t ∉ omegaCorePreimage S ∧ IsConj (z : G) (t : G) ∧
      IsElementaryAbelian 2 (centralizer ({t} : Set S)) ∧
      Nat.card (centralizer ({t} : Set S)) = 8 ∧
      ∀ V : Subgroup G, IsPGroup 2 V →
        (centralizer ({t} : Set S)).map (S : Subgroup G).subtype ≤ V →
        V ≤ centralizer ({(z : G), (t : G)} : Set G) →
        V = (centralizer ({t} : Set S)).map (S : Subgroup G).subtype := by
  obtain ⟨z, x, hz, hzC, hzR, _, hxR, hzx, _⟩ :=
    large_core_index_two_outside_centralizer_of_inside_fusion
      hns S hno W hunique hH hindex hinside
  obtain ⟨t, htz, hzt, hmax⟩ :=
    S.exists_distinct_conjugate_with_saturated_common_centralizer z hzC x
      (fun h => hxR (h ▸ hzR)) hzx
  have htR : t ∉ omegaCorePreimage S :=
    fun ht => htz (hinside z t hz hzC ht hzt)
  have ht : orderOf t = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hzt
    rw [← orderOf_coe t, ← hg, ← MulAut.conj_apply]
    simpa using ((MulAut.conj g).orderOf_eq (z : G)).trans ((orderOf_coe z).trans hz)
  let R := omegaCorePreimage S
  let : IsExtraspecial 2 R :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  let zR : R := ⟨z, hzR⟩
  have hzRorder : orderOf zR = 2 := (orderOf_coe zR).symm.trans hz
  let : IsElementaryAbelian 2 (centralizer ({t} : Set S)) :=
    S.elementary_centralizer_of_extraspecial_index_two_of_inside_fusion
      R hindex zR hzRorder hzC
      (fun u hu hzu => hinside z u hz hzC hu hzu) t
      (by simpa only [ht] using pow_orderOf_eq_one t) htR hzt
  have hstructure := large_core_index_two_elementary_centralizer_structure
    S hno W hunique hH hindex t ht htR
  exact ⟨z, t, hz, hzC, ht, htR, hzt, inferInstance, hstructure.2.2.1, hmax⟩

/-- Every elementary eight crossing the extraspecial core meets it in the
unique normal four and contains the core's central involution. -/
public theorem large_core_index_two_crossing_eight_structure
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hindex : (omegaCorePreimage S).index = 2)
    (F : Subgroup S) [IsElementaryAbelian 2 F] (hF : Nat.card F = 8)
    (hout : ¬ F ≤ omegaCorePreimage S) :
    omegaCorePreimage S ⊓ F = W ∧
      (center (omegaCorePreimage S)).map (omegaCorePreimage S).subtype ≤ F := by
  let R := omegaCorePreimage S
  let : IsExtraspecial 2 R :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  obtain ⟨hn, he, hc, hz⟩ :=
    elementary_eight_crossing_extraspecial_intersection hno R hindex F hF hout
  exact ⟨hunique (R ⊓ F) hn he hc, hz⟩

/-- The full elementary-eight normalizer count reduces to a lower bound
for eights crossing the core. The contained case and the upper bound are
unconditional consequences of the extraspecial and normal-only hypotheses. -/
public theorem large_core_index_two_normalizer_card_of_outside_bound
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 2)
    (houtside : ∀ F : Subgroup S, IsElementaryAbelian 2 F → Nat.card F = 8 →
      ¬ F ≤ omegaCorePreimage S → 32 ≤ Nat.card (normalizer (F : Set S))) :
    ∀ F : Subgroup S, IsElementaryAbelian 2 F → Nat.card F = 8 →
      Nat.card (normalizer (F : Set S)) = 32 := by
  intro F he hF
  let : IsElementaryAbelian 2 F := he
  have hS := card_sylow_of_large_core_index_two S hH hindex
  by_cases hFR : F ≤ omegaCorePreimage S
  · let R := omegaCorePreimage S
    let : IsExtraspecial 2 R :=
      IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
    have hR : Nat.card R = 32 := (card_omegaCorePreimage S).trans hH
    exact card_normalizer_eq_thirty_two_of_elementary_eight_le_extraspecial
      hS hno R hR F hF hFR
  · exact Nat.le_antisymm
      (card_normalizer_le_thirty_two_of_no_normal_eight hS hno F hF)
      (houtside F he hF hFR)

/-- Every elementary eight has normalizer of order thirty-two in the
index-two large-core case. The restriction is only on normal elementary
subgroups; the eight itself need not lie in the extraspecial core. -/
public theorem large_core_index_two_normalizer_card
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 2) :
    ∀ F : Subgroup S, IsElementaryAbelian 2 F → Nat.card F = 8 →
      Nat.card (normalizer (F : Set S)) = 32 := by
  apply large_core_index_two_normalizer_card_of_outside_bound S hno hH hindex
  intro F he hF hout
  let : IsElementaryAbelian 2 F := he
  let R := omegaCorePreimage S
  let : IsExtraspecial 2 R :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  have hR : Nat.card R = 32 := (card_omegaCorePreimage S).trans hH
  exact (card_normalizer_eq_thirty_two_of_elementary_eight_crossing_extraspecial
    (card_sylow_of_large_core_index_two S hH hindex) hno R hR hindex F hF hout).ge

end Stellmacher.Recognition.NormalEightNonnormalImage
