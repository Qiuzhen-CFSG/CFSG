module

public import Stellmacher.Recognition.NormalEightLargeCoreHigherIndexRankTwo
public import Stellmacher.Recognition.NormalEightRankTwoCyclicQuotient
public import Theory.GroupTheory.QuaternionDihedralCoreAction
public import Theory.GroupTheory.CoprimeInvolutionFusion

/-!
# The actual minus-core action and its involution orbit

Core-local rank identifies the extraspecial core of order thirty-two as
`Q₈ ∘ D₈`. Its actual five-point outer action has image of order twenty,
with cyclic Sylow two-subgroups of order four. Transport along the Sylow
embedding gives the cyclic-four quotient of the original Sylow subgroup.
The five-point action fuses the noncentral involutions of the core; the
odd-kernel lifting theorem gives their conjugacy in the original group.

Only the N₂ condition, central omega of order two, and core-local structure
are needed here. No ambient elementary-rank or fusion-exclusion hypothesis
is used.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

private theorem minus_core_four_dvd_index
    (S : Sylow 2 G) (hindex : 4 ≤ (omegaCorePreimage S).index) :
    4 ∣ (pCore 2 (OmegaQuotient S)).index := by
  obtain ⟨n, hn⟩ := (S.isPGroup'.to_quotient (omegaCorePreimage S)).exists_card_eq
  change (omegaCorePreimage S).index = 2 ^ n at hn
  have hnlo : 2 ≤ n := by
    by_contra h
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show n ≤ 1 by omega)
    omega
  have hd : 4 ∣ (omegaCorePreimage S).index := by
    rw [hn]
    exact Nat.pow_dvd_pow 2 hnlo
  rw [index_omegaCorePreimage] at hd
  exact hd.trans (relIndex_dvd_index_of_normal _ _)

/-- The actual outer action has image of order twenty, odd core of order five,
and cyclic Sylow two-subgroups of order four. -/
public theorem minus_core_action_range
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hcoreRank : ∀ E : Subgroup (pCore 2 (OmegaQuotient S)),
      IsElementaryAbelian 2 E → Nat.card E < 8)
    (hindex : 4 ≤ (omegaCorePreimage S).index) :
    Nat.card (pCoreCentralInvolutionAction (OmegaQuotient S)).range = 20 ∧
      Nat.card (pPrimeCore 2 (pCoreCentralInvolutionAction (OmegaQuotient S)).range) = 5 ∧
      ∀ P : Sylow 2 (pCoreCentralInvolutionAction (OmegaQuotient S)).range,
        Nat.card P = 4 ∧ IsCyclic P := by
  obtain ⟨B, C, hB, hC, hcomm, hjoin, _⟩ :=
    IsExtraspecial.dihedral_quaternion_factors_of_card_thirty_two hcoreRank hH
  exact quaternion_dihedral_pCore_action_range (omegaQuotient_solvable hN S hZ)
    (omegaQuotient_centralizer_pCore_le hN S hZ) hH B C hB hC hcomm hjoin
    (minus_core_four_dvd_index S hindex)

/-- The actual minus-core action forces the original Sylow quotient to be
cyclic of order four. -/
public theorem minus_core_index_four_and_isCyclic
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hcoreRank : ∀ E : Subgroup (pCore 2 (OmegaQuotient S)),
      IsElementaryAbelian 2 E → Nat.card E < 8)
    (hindex : 4 ≤ (omegaCorePreimage S).index) :
    (omegaCorePreimage S).index = 4 ∧ IsCyclic (S ⧸ omegaCorePreimage S) :=
  omegaCorePreimage_index_four_and_isCyclic_of_core_rank hN S hZ hH hcoreRank hindex

omit [Finite G] in
/-- For a center with omega of order two, its involution is unique. -/
private theorem minus_core_central_involution_unique
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z t : S) (hzC : z ∈ center S) (htC : t ∈ center S)
    (hz : orderOf z = 2) (ht : orderOf t = 2) : t = z := by
  let O := omega₁ (center S) (p := 2)
  have hmem (x : S) (hxC : x ∈ center S) (hx : orderOf x = 2) :
      (⟨x, hxC⟩ : center S) ∈ O := by
    apply Subgroup.subset_closure
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, pow_one, hx] using pow_orderOf_eq_one x
  let zO : O := ⟨⟨z, hzC⟩, hmem z hzC hz⟩
  let tO : O := ⟨⟨t, htC⟩, hmem t htC ht⟩
  have hzO : zO ≠ 1 := by
    intro heq
    have hz1 : z = 1 := congrArg (fun x : O => ((x : center S) : S)) heq
    simp [hz1] at hz
  have htO : tO ≠ 1 := by
    intro heq
    have ht1 : t = 1 := congrArg (fun x : O => ((x : center S) : S)) heq
    simp [ht1] at ht
  obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : O)).mp hZ
  exact congrArg (fun x : O => ((x : center S) : S)) ((hw tO htO).trans (hw zO hzO).symm)

/-- The odd kernel lifts an involution orbit in the quotient to actual
ambient conjugacy. -/
private theorem minus_core_isConj_of_omegaQuotient_isConj
    (S : Sylow 2 G) (x y : S) (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hconj : IsConj (omegaQuotientHom S x) (omegaQuotientHom S y)) :
    IsConj (x : G) (y : G) := by
  let q := QuotientGroup.mk' (pPrimeCore 2 (omegaNormalizer S))
  let i := inclusion (sylow_le_omegaNormalizer S)
  have h : IsConj (i x) (i y) := by
    apply q.isConj_of_map_isConj_of_involutions_of_odd_ker
      (QuotientGroup.mk'_surjective _)
      (by simpa only [q, QuotientGroup.ker_mk'] using
        (pPrimeCore_coprime_card (p := 2) (G := omegaNormalizer S)))
    · exact (orderOf_injective i (inclusion_injective _) x).trans hx
    · exact (orderOf_injective i (inclusion_injective _) y).trans hy
    · simpa only [q, i, omegaQuotientHom_apply, Subgroup.inclusion,
        MonoidHom.mk'_apply] using hconj
  exact (omegaNormalizer S).subtype.map_isConj h

/-- Every two core involutions distinct from the central Sylow involution
are conjugate in the original ambient group. -/
public theorem minus_core_noncentral_involutions_isConj
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hcoreRank : ∀ E : Subgroup (pCore 2 (OmegaQuotient S)),
      IsElementaryAbelian 2 E → Nat.card E < 8)
    (hindex : 4 ≤ (omegaCorePreimage S).index)
    (z : S) (hz : orderOf z = 2) (hzC : z ∈ center S)
    (x y : S) (hxH : x ∈ omegaCorePreimage S) (hx : orderOf x = 2) (hxz : x ≠ z)
    (hyH : y ∈ omegaCorePreimage S) (hy : orderOf y = 2) (hyz : y ≠ z) :
    IsConj (x : G) (y : G) := by
  let H := omegaCorePreimage S
  let : IsExtraspecial 2 H :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  let Z := (center H).map H.subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZcentral : Z ≤ center S := central_of_normal_card_two Z
    ((card_map_of_injective H.subtype_injective).trans (IsExtraspecial.center_order_p 2 H))
  have hncentral (u : H) (hu : orderOf (u : S) = 2) (huz : (u : S) ≠ z) :
      (⟨omegaQuotientHom S u, u.property⟩ : pCore 2 (OmegaQuotient S)) ∉
        center (pCore 2 (OmegaQuotient S)) := by
    intro huC
    have huHC : u ∈ center H := by
      apply mem_center_iff.mpr
      intro v
      apply Subtype.ext
      apply omegaQuotientHom_injective S
      have hc := congrArg Subtype.val
        (mem_center_iff.mp huC (⟨omegaQuotientHom S v, v.property⟩ : pCore 2 (OmegaQuotient S)))
      simpa only [coe_mul, map_mul] using hc
    exact huz (minus_core_central_involution_unique S hZ z u hzC
      (hZcentral (mem_map_of_mem H.subtype huHC)) hz hu)
  let xQ : pCore 2 (OmegaQuotient S) := ⟨omegaQuotientHom S x, hxH⟩
  let yQ : pCore 2 (OmegaQuotient S) := ⟨omegaQuotientHom S y, hyH⟩
  have hxQ : orderOf xQ = 2 := (orderOf_coe xQ).symm.trans
    ((orderOf_injective _ (omegaQuotientHom_injective S) x).trans hx)
  have hyQ : orderOf yQ = 2 := (orderOf_coe yQ).symm.trans
    ((orderOf_injective _ (omegaQuotientHom_injective S) y).trans hy)
  apply minus_core_isConj_of_omegaQuotient_isConj S x y hx hy
  exact extraspecial_pCore_noncentral_involutions_isConj_of_rank_two
    (omegaQuotient_solvable hN S hZ) (omegaQuotient_centralizer_pCore_le hN S hZ)
    hH hcoreRank (minus_core_four_dvd_index S hindex) xQ yQ
    hxQ (hncentral ⟨x, hxH⟩ hx hxz) hyQ (hncentral ⟨y, hyH⟩ hy hyz)

end Stellmacher.Recognition.NormalEightNonnormalImage
