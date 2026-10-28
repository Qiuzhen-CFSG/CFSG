module

public import Stellmacher.Recognition.NormalEightLargeCoreHigherIndexRankTwo
public import Stellmacher.Recognition.NormalEightLargeCoreRankTwoInsideFusion
public import Stellmacher.Recognition.NormalEightRankTwoBareSection
public import Stellmacher.Recognition.NormalEightRankTwoCyclicQuotient
public import Theory.GroupTheory.CoreFusionCentralizerDerived
public import Theory.GroupTheory.PGroup.CyclicFourSectionCentralization
public import Theory.GroupTheory.PGroup.MinusExtraspecialSquareAction

/-!
# Centralization of the quaternion–dihedral normalizer section

Inside-core weak closure and an abelian quotient by the core exclude the
central involution from the derived subgroup of every distinct fused
involution's Sylow centralizer. A cyclic-four section with central kernel
then centralizes the normal four. This uses only the normal elementary
bound, and does not require a saturated choice of the fused involution.

The intrinsic minus-core square-action calculation constructs the bare
cyclic-four section and its fixed-core bound. The faithful outer action
supplies the cyclic core quotient, and inside-core weak closure makes the
section centralize the normal four. Together these results discharge the
higher-index branch with core-local elementary rank at most two.

Source: Janko–Thompson (1970), §4, printed pp.389–390.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- Core-local weak closure and a cyclic core quotient supply the derived
exclusion used in the normalizer-section argument. -/
public theorem large_core_rank_two_centralizer_derived_excludes
    (S : Sylow 2 G) [IsCyclic (S ⧸ omegaCorePreimage S)]
    (z t : S) (hz : orderOf z = 2) (hzc : z ∈ center S) (hne : t ≠ z)
    (hzt : IsConj (z : G) (t : G))
    (hinside : ∀ u : S, orderOf u = 2 → u ∈ omegaCorePreimage S →
      IsConj (z : G) (u : G) → u = z) :
    z ∉ ⁅centralizer ({t} : Set S), centralizer ({t} : Set S)⁆ := by
  apply S.central_involution_not_mem_centralizer_derived_of_core_fusion
    (omegaCorePreimage S)
    (Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance)
    z t hzc hne hzt
  intro u hu hzu
  apply hinside u _ hu hzu
  obtain ⟨g, hg⟩ := isConj_iff.mp hzu
  rw [← orderOf_coe u, ← hg, ← MulAut.conj_apply]
  exact ((MulAut.conj g).orderOf_eq (z : G)).trans ((orderOf_coe z).trans hz)

/-- A bare cyclic-four section centralizes the normal four under core-local
weak closure. No elementary rank bound on the ambient Sylow is used. -/
public theorem large_core_rank_two_section_centralizes
    (S : Sylow 2 G) [IsCyclic (S ⧸ omegaCorePreimage S)]
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (z t : S) (hz : orderOf z = 2) (hzc : z ∈ center S) (ht : orderOf t = 2)
    (hne : t ≠ z) (hzt : IsConj (z : G) (t : G))
    (hinside : ∀ u : S, orderOf u = 2 → u ∈ omegaCorePreimage S →
      IsConj (z : G) (u : G) → u = z)
    (K : Subgroup S) (Z : Subgroup K) [Z.Normal] [IsCyclic (K ⧸ Z)]
    (hquot : Nat.card (K ⧸ Z) = 4)
    (hZK : Z ≤ (center S).comap K.subtype) (htK : t ∈ K) :
    K ≤ centralizer (W : Set S) := by
  have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hzW : z ∈ W := omega_one_center_le_normal_four_of_no_normal_eight hno W hW
    (show z ∈ (omega₁ (center S) (p := 2)).map (center S).subtype from
      ⟨⟨z, hzc⟩, subset_closure (show (⟨z, hzc⟩ : center S) ^ (2 ^ 1) = 1 from
        Subtype.ext (by simpa using hz2)), rfl⟩)
  exact cyclic_four_section_centralizes_of_not_mem_derived S.isPGroup' W hW
    z hz hzc hzW K Z hquot hZK ⟨t, htK⟩ (by
      apply Subtype.ext
      change t ^ 2 = 1
      simpa only [ht] using pow_orderOf_eq_one t)
    (large_core_rank_two_centralizer_derived_excludes S z t hz hzc hne hzt hinside)

/-- Once the core quotient and bare sections are constructed, the existing
inside-core fusion input completes the higher-index rank-two exclusion. -/
public theorem large_core_rank_two_false_of_cyclic_quotient_sections
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    [IsCyclic (S ⧸ omegaCorePreimage S)]
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hinside : ∀ z t : S, orderOf z = 2 → z ∈ center S → orderOf t = 2 →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z)
    (hsections : ∀ z t : S, orderOf z = 2 → z ∈ center S → orderOf t = 2 →
      t ∉ omegaCorePreimage S → IsConj (z : G) (t : G) →
      ∃ (K : Subgroup S) (Z : Subgroup K) (_ : Z.Normal),
        IsCyclic (K ⧸ Z) ∧ Nat.card (K ⧸ Z) = 4 ∧
        Z ≤ (center S).comap K.subtype ∧ t ∈ K ∧
        omegaCorePreimage S ⊓ centralizer ({t} : Set S) ≤ W) : False := by
  obtain ⟨z, t, hz, hzc, ht, hout, hzt⟩ :=
    large_core_rank_two_outside_conjugate_of_core_fusion hns S hZ hinside
  obtain ⟨K, Z, hZn, hcyclic, hquot, hZK, htK, hfixed⟩ :=
    hsections z t hz hzc ht hout hzt
  let : Z.Normal := hZn
  let : IsCyclic (K ⧸ Z) := hcyclic
  have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hzW : z ∈ W := omega_one_center_le_normal_four_of_no_normal_eight hno W hW
    (show z ∈ (omega₁ (center S) (p := 2)).map (center S).subtype from
      ⟨⟨z, hzc⟩, subset_closure (show (⟨z, hzc⟩ : center S) ^ (2 ^ 1) = 1 from
        Subtype.ext (by simpa using hz2)), rfl⟩)
  have hne : t ≠ z := fun he => hout (he ▸
    four_le_omegaCorePreimage hN S hZ W hW hno hzW)
  have hKW := large_core_rank_two_section_centralizes S hno W hW z t hz hzc ht
    hne hzt (hinside z · hz hzc) K Z hquot hZK htK
  exact large_core_rank_two_false_of_centralizing_section hN S hZ hno W hW hH
    K Z hquot hZK hKW ⟨t, htK⟩ (by
      apply Subtype.ext
      change t ^ 2 = 1
      simpa only [ht] using pow_orderOf_eq_one t) hfixed

/-- The intrinsic minus-core calculation supplies the bare section and its
fixed-core bound for every involution outside the core. -/
public theorem large_core_rank_two_bare_section
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hcoreRank : ∀ E : Subgroup (pCore 2 (OmegaQuotient S)),
      IsElementaryAbelian 2 E → Nat.card E < 8)
    (hindex : 4 ≤ (omegaCorePreimage S).index)
    (t : S) (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S) :
    ∃ (K : Subgroup S) (Z : Subgroup K) (_ : Z.Normal),
      IsCyclic (K ⧸ Z) ∧ Nat.card (K ⧸ Z) = 4 ∧
      Z ≤ (center S).comap K.subtype ∧ t ∈ K ∧
      omegaCorePreimage S ⊓ centralizer ({t} : Set S) ≤ W := by
  obtain ⟨hi, hcyclic⟩ :=
    omegaCorePreimage_index_four_and_isCyclic_of_core_rank hN S hZ hH hcoreRank hindex
  let : IsCyclic (S ⧸ omegaCorePreimage S) := hcyclic
  let : IsExtraspecial 2 (omegaCorePreimage S) :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  exact large_core_rank_two_bare_section_of_square_action hN S hZ W hunique hi
    (IsExtraspecial.square_action_fixed_four_of_card_thirty_two
      ((card_omegaCorePreimage S).trans hH)
      (fun E hE => @omegaCorePreimage_elementary_card_lt_eight G _ _ S hcoreRank E hE))
    t ht hout

/-- A fused outside involution lies in a cyclic-four section with central
kernel that centralizes the normal four, and its fixed core lies in that four.
Only elementary subgroups inside the core are subject to a rank bound. -/
public theorem large_core_rank_two_section
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
      IsElementaryAbelian 2 E → Nat.card E < 8)
    (z t : S) (hz : orderOf z = 2) (hzc : z ∈ center S) (ht : orderOf t = 2)
    (hout : t ∉ omegaCorePreimage S) (hzt : IsConj (z : G) (t : G)) :
    ∃ (K : Subgroup S) (Z : Subgroup K) (_ : Z.Normal),
      IsCyclic (K ⧸ Z) ∧ Nat.card (K ⧸ Z) = 4 ∧
      Z ≤ (center S).comap K.subtype ∧ K ≤ centralizer (W : Set S) ∧
      t ∈ K ∧ omegaCorePreimage S ⊓ centralizer ({t} : Set S) ≤ W := by
  obtain ⟨_, hcyclic⟩ :=
    omegaCorePreimage_index_four_and_isCyclic_of_core_rank hN S hZ hH hcoreRank hindex
  let : IsCyclic (S ⧸ omegaCorePreimage S) := hcyclic
  obtain ⟨K, Z, hZn, hKcyclic, hquot, hZK, htK, hfixed⟩ :=
    large_core_rank_two_bare_section hN S hZ W hunique hH hcoreRank hindex t ht hout
  let : Z.Normal := hZn
  let : IsCyclic (K ⧸ Z) := hKcyclic
  have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hzW : z ∈ W := omega_one_center_le_normal_four_of_no_normal_eight hno W hW
    (show z ∈ (omega₁ (center S) (p := 2)).map (center S).subtype from
      ⟨⟨z, hzc⟩, subset_closure (show (⟨z, hzc⟩ : center S) ^ (2 ^ 1) = 1 from
        Subtype.ext (by simpa using hz2)), rfl⟩)
  have hne : t ≠ z := fun he => hout (he ▸
    four_le_omegaCorePreimage hN S hZ W hW hno hzW)
  have hinside := large_core_rank_two_inside_fusion hN S hZ hno W hW hunique
    hH hindex hcoreRank
  exact ⟨K, Z, hZn, hKcyclic, hquot, hZK,
    large_core_rank_two_section_centralizes S hno W hW z t hz hzc ht hne hzt
      (hinside z · hz hzc) K Z hquot hZK htK, htK, hfixed⟩

/-- The higher-index extraspecial core of order thirty-two and core-local
elementary rank at most two is impossible under the normal-only hypotheses. -/
public theorem large_core_rank_two_false
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
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
      IsElementaryAbelian 2 E → Nat.card E < 8) : False := by
  obtain ⟨z, t, hz, hzc, ht, hout, hzt⟩ :=
    large_core_rank_two_outside_conjugate_of_core_fusion hns S hZ
      (large_core_rank_two_inside_fusion hN S hZ hno W hW hunique hH hindex hcoreRank)
  obtain ⟨K, Z, hZn, hcyclic, hquot, hZK, hKW, htK, hfixed⟩ :=
    large_core_rank_two_section hN S hZ hno W hW hunique hH hindex hcoreRank
      z t hz hzc ht hout hzt
  let : Z.Normal := hZn
  let : IsCyclic (K ⧸ Z) := hcyclic
  exact large_core_rank_two_false_of_centralizing_section hN S hZ hno W hW hH
    K Z hquot hZK hKW ⟨t, htK⟩ (by
      apply Subtype.ext
      change t ^ 2 = 1
      simpa only [ht] using pow_orderOf_eq_one t) hfixed

end Stellmacher.Recognition.NormalEightNonnormalImage
