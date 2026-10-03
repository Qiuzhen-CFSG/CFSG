module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Stellmacher.Recognition.SimpleInvolutionFusion
public import Theory.GroupTheory.QuaternionCentralProductSylowIndex
public import Theory.GroupTheory.CoreInvolutionFusion
public import Stellmacher.Recognition.NormalEightQuaternionOuterAction
public import Theory.GroupTheory.QuaternionCentralProductInvolutionCentralizers
public import Theory.GroupTheory.CoprimeInvolutionFusion

/-!
# Higher-index quaternion cores in the central-omega quotient

For the actual quotient core with two supplied quaternion factors, the
self-centralizing action bounds the Sylow index by eight. The index is a
power of two, so an index at least four is four or eight. At index four the
quotient is cyclic or elementary abelian; at index eight the actual outer
action identifies the quotient as dihedral. Its order-nine subgroup fuses
the noncentral core involutions. The intrinsic centralizer geometry then
feeds the normalizer argument producing a conjugate of the central
involution outside the core. Conjugacy in the central-omega quotient lifts
through its odd kernel to the original ambient group.

Source: Janko–Thompson (1970), §4, printed pp.390–391.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- The original Sylow quotient is the actual quotient Sylow modulo its core,
not merely a group with the same order. -/
public theorem quaternion_core_quotient_equiv
    (S : Sylow 2 G) :
    Nonempty ((S ⧸ omegaCorePreimage S) ≃*
      ((omegaQuotientSylow S) ⧸
        (pCore 2 (OmegaQuotient S)).subgroupOf (omegaQuotientSylow S))) := by
  let e := omegaQuotientSylowEquiv S
  refine ⟨QuotientGroup.congr _ _ e ?_⟩
  ext u
  change u ∈ (omegaCorePreimage S).map e.toMonoidHom ↔ _
  rw [mem_map_equiv]
  change omegaQuotientHom S (e.symm u) ∈ pCore 2 (OmegaQuotient S) ↔
    (u : OmegaQuotient S) ∈ pCore 2 (OmegaQuotient S)
  have h : omegaQuotientHom S (e.symm u) = (u : OmegaQuotient S) := by
    rw [← omegaQuotientSylowEquiv_apply]
    exact congrArg Subtype.val (e.apply_symm_apply u)
  rw [h]

/-- The odd kernel lifts an involution orbit in the quotient to actual
ambient conjugacy. -/
public theorem isConj_of_omegaQuotient_isConj
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

/-- The quaternion factor bound applies to the original Sylow core preimage. -/
public theorem quaternion_core_index_le_eight
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) :
    (omegaCorePreimage S).index ≤ 8 := by
  rw [index_omegaCorePreimage]
  exact sylow_relIndex_le_eight_of_quaternion_factors _
    (omegaQuotient_centralizer_pCore_le hN S hZ)
    (IsExtraspecial.center_order_p 2 _) hH B C hB hC hinter hcomm hjoin _

/-- The order bound gives exactly two possible indices; it does not identify
an order-eight quotient. -/
public theorem quaternion_core_index_four_or_eight
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hindex : 4 ≤ (omegaCorePreimage S).index) :
    (omegaCorePreimage S).index = 4 ∨ (omegaCorePreimage S).index = 8 := by
  have hbound := quaternion_core_index_le_eight hN S hZ hH B C hB hC hjoin hinter hcomm
  obtain ⟨n, hn⟩ := (S.isPGroup'.to_quotient (omegaCorePreimage S)).exists_card_eq
  change (omegaCorePreimage S).index = 2 ^ n at hn
  have hnlo : 2 ≤ n := by
    by_contra h
    have : n ≤ 1 := by omega
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) this
    omega
  have hnhi : n ≤ 3 := by
    by_contra h
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show 4 ≤ n by omega)
    norm_num at hp
    omega
  interval_cases n <;> simp_all

/-- Both order-four quotient types are exhausted without any extra action
hypothesis. -/
public theorem quaternion_core_quotient_cases_or_order_eight
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hindex : 4 ≤ (omegaCorePreimage S).index) :
    ((omegaCorePreimage S).index = 4 ∧ IsCyclic (S ⧸ omegaCorePreimage S)) ∨
      ((omegaCorePreimage S).index = 4 ∧ IsElementaryAbelian 2 (S ⧸ omegaCorePreimage S)) ∨
      (omegaCorePreimage S).index = 8 := by
  classical
  rcases quaternion_core_index_four_or_eight hN S hZ hH B C hB hC hjoin hinter hcomm hindex
      with hfour | height
  · by_cases hc : IsCyclic (S ⧸ omegaCorePreimage S)
    · exact Or.inl ⟨hfour, hc⟩
    · have hcard : Nat.card (S ⧸ omegaCorePreimage S) = 2 ^ 2 := hfour
      exact Or.inr (Or.inl ⟨hfour, {
        toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
        exponent_dvd_p := by
          rw [(not_isCyclic_iff_exponent_eq_prime Nat.prime_two hcard).mp hc] }⟩)
  · exact Or.inr (Or.inr height)

omit [Finite G] in
/-- For a center with omega of order two, its involution is unique. -/
private theorem central_involution_unique
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

/-- Source fusion assembly with explicit orbit and core-centralizer inputs.
The orbit and geometry premises remain mathematical obligations; no outside
fusion or weak-closure premise is assumed. -/
public theorem quaternion_core_outside_conjugate_of_orbit_and_geometry
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (horbit : ∀ z : S, orderOf z = 2 → z ∈ center S →
      ∀ x ∈ omegaCorePreimage S, orderOf x = 2 → x ≠ z →
      ∀ y ∈ omegaCorePreimage S, orderOf y = 2 → y ≠ z → IsConj (x : G) (y : G))
    (hgeometry : ∀ z : S, orderOf z = 2 → z ∈ center S →
      ∀ t ∈ omegaCorePreimage S, orderOf t = 2 → t ≠ z →
      let D := omegaCorePreimage S ⊓ centralizer ({t} : Set S)
      closure {x : S | x ∈ D ∧ orderOf x = 2} = D ∧
      (_root_.commutator D).map D.subtype = zpowers z) :
    ∃ z t : S, orderOf z = 2 ∧ z ∈ center S ∧ orderOf t = 2 ∧
      t ∉ omegaCorePreimage S ∧ IsConj (z : G) (t : G) := by
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let z : S := (w : center S)
  have hz : orderOf z = 2 :=
    (orderOf_coe (w : center S)).trans ((orderOf_coe w).trans hw)
  have hzC : z ∈ center S := (w : center S).property
  obtain ⟨t, ht, htH, hzt⟩ := S.exists_conjugate_outside_of_core_involution_geometry
    (omegaCorePreimage S) z hz hzC
    (fun t _ htC ht => central_involution_unique S hZ z t hzC htC hz ht)
    (exists_distinct_isConj_in_sylow hns S z hz)
    (horbit z hz hzC) (hgeometry z hz hzC)
  exact ⟨z, t, hz, hzC, ht, htH, hzt⟩



/-- The quaternion core has precisely the cyclic-four, elementary-four, or
dihedral-eight Sylow quotient occurring in the source. -/
public theorem quaternion_core_quotient_cases
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hindex : 4 ≤ (omegaCorePreimage S).index) :
    ((omegaCorePreimage S).index = 4 ∧ IsCyclic (S ⧸ omegaCorePreimage S)) ∨
      ((omegaCorePreimage S).index = 4 ∧ IsElementaryAbelian 2 (S ⧸ omegaCorePreimage S)) ∨
      Nonempty ((S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4) := by
  rcases quaternion_core_quotient_cases_or_order_eight
      hN S hZ hH B C hB hC hjoin hinter hcomm hindex with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (quaternion_outer_action_index_eight_dihedral
      hN S hZ hH B C hB hC hjoin hinter hcomm h))

/-- The source outside-fusion conclusion for the supplied actual quaternion
core. The actual order-nine action supplies the orbit, and the intrinsic
quaternion centralizer calculation supplies its involution generators and
commutator line. -/
public theorem quaternion_core_outside_conjugate
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hindex : 4 ≤ (omegaCorePreimage S).index) :
    ∃ z t : S, orderOf z = 2 ∧ z ∈ center S ∧ orderOf t = 2 ∧
      t ∉ omegaCorePreimage S ∧ IsConj (z : G) (t : G) := by
  classical
  let H := omegaCorePreimage S
  let e := omegaCorePreimageEquiv S
  let : IsExtraspecial 2 H := IsExtraspecial.of_mulEquiv e.symm inferInstance
  let Z := (center H).map H.subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZcentral : Z ≤ center S := central_of_normal_card_two Z
    ((card_map_of_injective H.subtype_injective).trans (IsExtraspecial.center_order_p 2 H))
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := center H) 2
    (by rw [IsExtraspecial.center_order_p 2 H])
  have hwS : orderOf ((w : H) : S) = 2 :=
    (orderOf_coe (w : H)).trans ((orderOf_coe w).trans hw)
  have hwC : ((w : H) : S) ∈ center S :=
    hZcentral (mem_map_of_mem H.subtype w.property)
  have hzmem (z : S) (hz : orderOf z = 2) (hzC : z ∈ center S) : z ∈ H := by
    have heq := central_involution_unique S hZ z (w : H) hzC hwC hz hwS
    exact heq ▸ (w : H).property
  have hncentral (z : S) (hz : orderOf z = 2) (hzC : z ∈ center S)
      (x : H) (hx : orderOf (x : S) = 2) (hxz : (x : S) ≠ z) :
      (⟨omegaQuotientHom S x, x.property⟩ : pCore 2 (OmegaQuotient S)) ∉
        center (pCore 2 (OmegaQuotient S)) := by
    intro hxC
    have hxHC : x ∈ center H := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      apply omegaQuotientHom_injective S
      have hc := congrArg Subtype.val
        (mem_center_iff.mp hxC (⟨omegaQuotientHom S y, y.property⟩ : pCore 2 (OmegaQuotient S)))
      simpa only [coe_mul, map_mul] using hc
    exact hxz (central_involution_unique S hZ z x hzC
      (hZcentral (mem_map_of_mem H.subtype hxHC)) hz hx)
  obtain ⟨U, hU⟩ := quaternion_core_exists_nine_subgroup
    hN S hZ hH B C hB hC hjoin hinter hcomm hindex
  apply quaternion_core_outside_conjugate_of_orbit_and_geometry hns S hZ
  · intro z hz hzC x hxH hx hxz y hyH hy hyz
    let xH : H := ⟨x, hxH⟩
    let yH : H := ⟨y, hyH⟩
    let xQ : pCore 2 (OmegaQuotient S) := ⟨omegaQuotientHom S x, hxH⟩
    let yQ : pCore 2 (OmegaQuotient S) := ⟨omegaQuotientHom S y, hyH⟩
    have hxQ : orderOf xQ = 2 := (orderOf_coe xQ).symm.trans
      ((orderOf_injective _ (omegaQuotientHom_injective S) x).trans hx)
    have hyQ : orderOf yQ = 2 := (orderOf_coe yQ).symm.trans
      ((orderOf_injective _ (omegaQuotientHom_injective S) y).trans hy)
    apply isConj_of_omegaQuotient_isConj S x y hx hy
    exact quaternion_core_noncentral_involution_conjugacy hN S hZ hH
      B C hB hC hjoin hinter hcomm U hU xQ yQ
      hxQ (hncentral z hz hzC xH hx hxz) hyQ (hncentral z hz hzC yH hy hyz)
  · intro z hz hzC t htH ht htz
    let B' := B.map e.symm.toMonoidHom
    let C' := C.map e.symm.toMonoidHom
    have hB' : Nonempty (B' ≃* QuaternionGroup 2) :=
      hB.map (fun f => (B.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans f)
    have hC' : Nonempty (C' ≃* QuaternionGroup 2) :=
      hC.map (fun f => (C.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans f)
    have hjoin' : B' ⊔ C' = ⊤ := by
      rw [← Subgroup.map_sup, hjoin, map_top_of_surjective _ e.symm.surjective]
    have hinter' : Nat.card (B' ⊓ C' : Subgroup H) = 2 := by
      rw [← map_inf _ _ _ e.symm.injective,
        card_map_of_injective e.symm.injective, hinter]
    have hcomm' : ∀ b ∈ B', ∀ c ∈ C', b * c = c * b := by
      rintro b ⟨b₀, hb₀, rfl⟩ c ⟨c₀, hc₀, rfl⟩
      exact (map_mul e.symm.toMonoidHom b₀ c₀).symm.trans
        ((congrArg e.symm.toMonoidHom (hcomm b₀ hb₀ c₀ hc₀)).trans
          (map_mul e.symm.toMonoidHom c₀ b₀))
    exact quaternion_central_product_involution_centralizer_geometry_in_ambient
      H B' C' hB' hC' hjoin' hinter' hcomm' z t hz hzC (hzmem z hz hzC) ht htH htz

end Stellmacher.Recognition.NormalEightNonnormalImage
