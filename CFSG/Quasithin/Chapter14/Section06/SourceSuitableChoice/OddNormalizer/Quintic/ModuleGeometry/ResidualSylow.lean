module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ResidualIndex
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Dimensions
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.GroupTheory.SpecificGroups.DihedralEightRecognition

/-!
# The actual dihedral action in the residual branch

Conjugation by H on O²(H)/O₂(O²(H)) has kernel equal to the preimage
of O²(H/O₂(H)). Self-centralization of the residual in the core-free
quotient and the odd elementary plane prove this equality. On the original
Sylow T this is precisely the kernel of T → H/O₂(H).

Consequently the literal Sylow action image has order eight. H supplies
the same image, and the original H₀ supplies an elementary four-subgroup.
The exchanging element prevents this four-subgroup from being central:
otherwise its order-four image would be an image of an order-ten actor.
Dihedral-eight recognition therefore identifies the actual Sylow image.

ResidualSigned uses this source input to mark the image by signed matrices
and discharge the normalizer index in ResidualIndex. The exchanged module
geometry, remaining component comparisons and final p=3 assembly remain
with qt-e-14615-quintic-exclusion. The original 14.6.12 index is used;
no proof without ExchangedFactorSetup.index is asserted. Earlier-source
14.6.12--14 discharge remains with qt-e-suitable-odd-normalizer.

Source: Aschbacher--Smith 14.6.12 and 14.6.15, printed pp.1031,1034.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentExclusion ComponentExclusion.ContainedComparison
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)

include s in
private theorem original_partner_contains : H ≤ Mc := by
  have he := (Section02.source_lemma_14_2_3 s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action H s.outside.1 s.outside.2).1
  exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2

include s in
/-- On H, the literal intrinsic residual action is trivial precisely over
its starred residual. This is a quotient-kernel statement. -/
theorem source_residual_action_eq_one_iff
    (hc : residualClosure H Mc = residual H) (x : Mc) (hx : (x : G) ∈ H) :
    residualPartnerAction Mc H hc x = 1 ↔
      QuotientGroup.mk' (pCore 2 H) ⟨x,hx⟩ ∈ pResidual 2 (H ⧸ pCore 2 H) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let := s.primitive.elementary
  let R := pResidual 2 (H ⧸ pCore 2 H)
  let q := QuotientGroup.mk' (pCore 2 H)
  obtain ⟨c,hcmap⟩ := residual_quotient_equiv (by decide : Odd 5) H
    (IsElementaryAbelian.isPGroup 5 R)
  have hcompat (v : residual H ⧸ pCore 2 (residual H)) :
      (c (residualPartnerAction Mc H hc x v) : H ⧸ pCore 2 H) =
        q ⟨x,hx⟩ * (c v : H ⧸ pCore 2 H) * (q ⟨x,hx⟩)⁻¹ := by
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (residual H)) v
    change (c (pCoreNormalizerAction 2 (residual H)
      (inclusion (residual_partner_normalizes Mc H hc) x)
        (QuotientGroup.mk' (pCore 2 (residual H)) v)) : H ⧸ pCore 2 H) = _
    rw [pCoreNormalizerAction_mk,hcmap,hcmap]
    change q _ = q ⟨x,hx⟩ * q _ * (q ⟨x,hx⟩)⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    rfl
  constructor
  · intro hact
    apply centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2)
    intro r hr
    have hh := hcompat (c.symm ⟨r,hr⟩)
    simp only [hact, MulAut.one_apply, c.apply_symm_apply] at hh
    change r = q ⟨x,hx⟩ * r * (q ⟨x,hx⟩)⁻¹ at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  · intro hr
    apply MulEquiv.ext
    intro v
    apply c.injective
    apply Subtype.ext
    rw [hcompat]
    change q ⟨x,hx⟩ * (c v : H ⧸ pCore 2 H) * (q ⟨x,hx⟩)⁻¹ = (c v : H ⧸ pCore 2 H)
    have hh : q ⟨x,hx⟩ * (c v : H ⧸ pCore 2 H) = (c v : H ⧸ pCore 2 H) * q ⟨x,hx⟩ :=
      congrArg Subtype.val (mul_comm (⟨q ⟨x,hx⟩,hr⟩ : R) (c v))
    rw [hh,mul_inv_cancel_right]

include s in
/-- The original Sylow's intrinsic residual-action kernel is exactly its
kernel in H/O₂(H). No signed coordinates are assumed. -/
theorem source_residual_sylow_action_kernel
    (hc : residualClosure H Mc = residual H) :
    ((residualPartnerAction Mc H hc).comp
      (inclusion (source_residual_partner_sylow_le s))).ker =
    ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion s.outside.1.2)).ker := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let := s.primitive.elementary
  let q := QuotientGroup.mk' (pCore 2 H)
  let S := (T.subtype s.outside.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hd : Disjoint (S : Subgroup (H ⧸ pCore 2 H)) (pResidual 2 (H ⧸ pCore 2 H)) :=
    IsPGroup.disjoint_of_coprime S.isPGroup' (IsElementaryAbelian.isPGroup 5 _) (by decide)
  ext x
  change residualPartnerAction Mc H hc ⟨x,source_residual_partner_sylow_le s x.property⟩ = 1 ↔
    q ⟨x,s.outside.1.2 x.property⟩ = 1
  rw [source_residual_action_eq_one_iff s hc _ (s.outside.1.2 x.property)]
  constructor
  · intro hx
    exact Subgroup.disjoint_def.mp hd
      (mem_map_of_mem q (show (⟨x,s.outside.1.2 x.property⟩ : H) ∈
        (T : Subgroup G).subgroupOf H from x.property)) hx
  · intro hx
    rw [hx]
    exact one_mem _

include s in
/-- The Sylow image on the actual intrinsic residual quotient has order eight. -/
theorem source_residual_sylow_action_card
    (hc : residualClosure H Mc = residual H) :
    Nat.card (((T : Subgroup G).subgroupOf Mc).map (residualPartnerAction Mc H hc)) = 8 := by
  let f := (residualPartnerAction Mc H hc).comp
    (inclusion (source_residual_partner_sylow_le s))
  let q := QuotientGroup.mk' (pCore 2 H)
  let qT := q.comp (inclusion s.outside.1.2)
  let S := (T.subtype s.outside.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hf : ((T : Subgroup G).subgroupOf Mc).map (residualPartnerAction Mc H hc) = f.range := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x,source_residual_partner_sylow_le s x.property⟩,x.property,rfl⟩
  have hq : (S : Subgroup (H ⧸ pCore 2 H)) = qT.range := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x,s.outside.1.2 x.property⟩,x.property,rfl⟩
  have hk : f.ker = qT.ker := source_residual_sylow_action_kernel s hc
  rw [hf,←index_ker,hk,index_ker,←hq]
  rw [S.card_eq_multiplicity,OddCriticalPair.exchanged_actor_card a (T : Subgroup G) 5 H0 H1 H2 s.factors]
  rw [show 8 * 5^2 = 2^3 * 5^2 by decide, Nat.factorization_mul (by decide) (by decide)]
  have h8 : Nat.factorization 8 2 = 3 := Nat.factorization_pow_self (n := 3) Nat.prime_two
  have h25 : Nat.factorization 25 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  change 2 ^ (Nat.factorization 8 2 + Nat.factorization 25 2) = 8
  rw [h8,h25]
  rfl

include s in
/-- The literal H-action is already supplied by T, since the residual acts
internally on an abelian quotient. -/
theorem source_residual_H_action_image
    (hc : residualClosure H Mc = residual H) :
    (H.subgroupOf Mc).map (residualPartnerAction Mc H hc) =
      ((T : Subgroup G).subgroupOf Mc).map (residualPartnerAction Mc H hc) := by
  let f := residualPartnerAction Mc H hc
  have hHM := original_partner_contains s
  have hKM : residual H ≤ Mc := (residual_le H).trans hHM
  have hTM := source_residual_partner_sylow_le s
  have hKker : (residual H).subgroupOf Mc ≤ f.ker := by
    intro x hx
    apply (source_residual_action_eq_one_iff s hc x (residual_le H hx)).mpr
    have hxH : (x : G) ∈ H := residual_le H hx
    obtain ⟨y,hy,he⟩ := hx
    have hmap := mem_map_of_mem (QuotientGroup.mk' (pCore 2 H)) hy
    rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)] at hmap
    have hxy : (⟨(x : G),hxH⟩ : H) = y := Subtype.ext he.symm
    rw [hxy]
    exact hmap
  have hj : residual H ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype s.outside.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change residual H ⊔ (((T : Subgroup G).subgroupOf H).map H.subtype) = H at hh
    rwa [map_subgroupOf_eq_of_le s.outside.1.2] at hh
  change (H.subgroupOf Mc).map f = ((T : Subgroup G).subgroupOf Mc).map f
  have hjM : H.subgroupOf Mc = (residual H).subgroupOf Mc ⊔ (T : Subgroup G).subgroupOf Mc := by
    rw [←subgroupOf_sup hKM hTM,hj]
  have hz : ((residual H).subgroupOf Mc).map f = ⊥ := by
    apply bot_unique
    rintro y ⟨x,hx,rfl⟩
    exact hKker hx
  rw [hjM,Subgroup.map_sup,hz,bot_sup_eq]

include s in
/-- The complete H-image has order eight, on the literal residual quotient. -/
theorem source_residual_H_action_card
    (hc : residualClosure H Mc = residual H) :
    Nat.card ((H.subgroupOf Mc).map (residualPartnerAction Mc H hc)) = 8 := by
  rw [source_residual_H_action_image s hc]
  exact source_residual_sylow_action_card s hc

include s in
private theorem local_action_kernel_le_first_pair
    (hc : residualClosure H Mc = residual H) :
    ((residualPartnerAction Mc H hc).comp (inclusion (original_partner_contains s))).ker ≤
      H0.subgroupOf H := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hK : pResidual 2 H ≤ H0.subgroupOf H := by
    intro x hx
    exact residual_le_of_index_two H0 s.factors.zero_le s.factors.index
      (mem_map_of_mem H.subtype hx)
  have hQ : q.ker ≤ H0.subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact s.factors.first_le (s.factors.core_le_first (mem_map_of_mem H.subtype hx))
  intro x hx
  have hr := (source_residual_action_eq_one_iff s hc
    ⟨x,original_partner_contains s x.property⟩ x.property).mp hx
  rw [←map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)] at hr
  have hm : x ∈ ((pResidual 2 H).map q).comap q := hr
  rw [comap_map_eq] at hm
  exact sup_le hK hQ hm

include s in
/-- The original factor stabilizer has image of index two in the Sylow image. -/
theorem source_residual_pair_action_index
    (hc : residualClosure H Mc = residual H) :
    ((H0.subgroupOf Mc).map (residualPartnerAction Mc H hc)).relIndex
      (((T : Subgroup G).subgroupOf Mc).map (residualPartnerAction Mc H hc)) = 2 := by
  let f := residualPartnerAction Mc H hc
  let fH := f.comp (inclusion (original_partner_contains s))
  have hA : (H0.subgroupOf Mc).map f = (H0.subgroupOf H).map fH := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,s.factors.zero_le hx⟩,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,original_partner_contains s x.property⟩,hx,rfl⟩
  have hB : (H.subgroupOf Mc).map f = (⊤ : Subgroup H).map fH := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,mem_top _,rfl⟩
    · rintro ⟨x,_,rfl⟩
      exact ⟨⟨x,original_partner_contains s x.property⟩,x.property,rfl⟩
  rw [←source_residual_H_action_image s hc]
  change ((H0.subgroupOf Mc).map f).relIndex ((H.subgroupOf Mc).map f) = 2
  rw [hA,hB,relIndex_map_map,sup_of_le_left (local_action_kernel_le_first_pair s hc),
    top_sup_eq,relIndex_top_right]
  exact s.factors.index

include s in
/-- The literal H₀-image is a four-subgroup of the actual residual-action image. -/
theorem source_residual_pair_action_card
    (hc : residualClosure H Mc = residual H) :
    Nat.card ((H0.subgroupOf Mc).map (residualPartnerAction Mc H hc)) = 4 := by
  let f := residualPartnerAction Mc H hc
  let A := (H0.subgroupOf Mc).map f
  let B := (H.subgroupOf Mc).map f
  have hAB : A ≤ B := map_mono (subgroupOf_mono Mc s.factors.zero_le)
  have hi : A.relIndex B = 2 := by
    change ((H0.subgroupOf Mc).map f).relIndex ((H.subgroupOf Mc).map f) = 2
    rw [source_residual_H_action_image s hc]
    exact source_residual_pair_action_index s hc
  have hh := (A.subgroupOf B).card_mul_index
  change Nat.card (A.subgroupOf B) * A.relIndex B = Nat.card B at hh
  rw [Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv,hi,source_residual_H_action_card s hc] at hh
  change Nat.card ((H0.subgroupOf Mc).map (residualPartnerAction Mc H hc)) * 2 = 8 at hh
  omega

include s in
/-- Each element of the original factor stabilizer squares to the literal
residual-action kernel. The independent factor models are essential here. -/
theorem source_residual_pair_action_square
    (hc : residualClosure H Mc = residual H) (x : Mc) (hx : (x : G) ∈ H0) :
    residualPartnerAction Mc H hc x ^ 2 = 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  let A := actorImage H H1
  let B := actorImage H H2
  have hsquare (D : Subgroup (H ⧸ pCore 2 H)) (hd : Nat.card D = 10) (d : D) :
      (d : H ⧸ pCore 2 H)^2 ∈ pResidual 2 (H ⧸ pCore 2 H) := by
    have hr : Nat.card (pResidual 2 D) = 5 :=
      card_twoResidual_of_card_twice_odd_prime (by decide : Odd 5) hd
    have hi : (pResidual 2 D).index = 2 := by
      have hh := (pResidual 2 D).card_mul_index
      rw [hr,hd] at hh
      omega
    exact map_pResidual_le 2 D.subtype (mem_map_of_mem D.subtype (sq_mem_of_index_two hi d))
  have hxAB : q ⟨x,s.factors.zero_le hx⟩ ∈ A ⊔ B := by
    have he : A ⊔ B = actorImage H H0 := by
      change actorImage H H1 ⊔ actorImage H H2 = actorImage H H0
      unfold actorImage
      rw [←Subgroup.map_sup,←subgroupOf_sup (s.factors.first_le.trans s.factors.zero_le)
        (s.factors.second_le.trans s.factors.zero_le),s.factors.join_eq]
    rw [he]
    exact mem_map_of_mem q hx
  have hn : A ≤ normalizer (B : Set (H ⧸ pCore 2 H)) :=
    actorImage_normalizes H2 H1 (s.factors.second_le.trans s.factors.zero_le)
      (s.factors.first_le.trans s.factors.normalizes_second)
  have hm : q ⟨x,s.factors.zero_le hx⟩ ∈ (A : Set (H ⧸ pCore 2 H)) * (B : Set (H ⧸ pCore 2 H)) := by
    rw [←coe_mul_of_left_le_normalizer_right A B hn]
    exact hxAB
  obtain ⟨u,hu,v,hv,he⟩ := hm
  rw [←map_pow]
  apply (source_residual_action_eq_one_iff s hc (x^2) (H.pow_mem (s.factors.zero_le hx) 2)).mpr
  change q (⟨x,s.factors.zero_le hx⟩ ^ 2) ∈ _
  rw [map_pow,←he,(s.factors.actors_commute u hu v hv).mul_pow]
  apply (pResidual 2 (H ⧸ pCore 2 H)).mul_mem
  · apply hsquare A _ ⟨u,hu⟩
    rw [Nat.card_congr s.factors.first_model.some.toEquiv,DihedralGroup.nat_card]
  · apply hsquare B _ ⟨v,hv⟩
    rw [Nat.card_congr s.factors.second_model.some.toEquiv,DihedralGroup.nat_card]

include s in
/-- The marked index-two image is elementary abelian of order four. -/
theorem source_residual_pair_action_elementary
    (hc : residualClosure H Mc = residual H) :
    IsElementaryAbelian 2 ((H0.subgroupOf Mc).map (residualPartnerAction Mc H hc)) := by
  let D := (H0.subgroupOf Mc).map (residualPartnerAction Mc H hc)
  have hcard : Nat.card D = 2^2 := source_residual_pair_action_card s hc
  let : IsMulCommutative D := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  rintro ⟨y,x,hx,rfl⟩
  apply Subtype.ext
  exact source_residual_pair_action_square s hc x hx

include s in
private theorem action_subgroup_card_dvd
    (hc : residualClosure H Mc = residual H) (A : Subgroup G) (hAH : A ≤ H) :
    Nat.card ((A.subgroupOf Mc).map (residualPartnerAction Mc H hc)) ∣
      Nat.card (actorImage H A) := by
  have hAM := hAH.trans (original_partner_contains s)
  let f := (residualPartnerAction Mc H hc).comp (inclusion hAM)
  let q := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hAH)
  have hk : q.ker ≤ f.ker := by
    intro x hx
    apply (source_residual_action_eq_one_iff s hc ⟨x,hAM x.property⟩ (hAH x.property)).mpr
    change (QuotientGroup.mk' (pCore 2 H)) ⟨x,hAH x.property⟩ = 1 at hx
    rw [hx]
    exact one_mem _
  have hf : ((A.subgroupOf Mc).map (residualPartnerAction Mc H hc)) = f.range := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x,hAM x.property⟩,x.property,rfl⟩
  have hq : actorImage H A = q.range := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x,hAH x.property⟩,x.property,rfl⟩
  rw [hf,hq,←index_ker,←index_ker]
  exact index_dvd_of_le hk

include s in
/-- The marked four-image is not central in the actual Sylow image: the
original exchanging element would otherwise identify the two factor images,
forcing an order-four image of an order-ten dihedral actor. -/
theorem source_residual_pair_action_not_central
    (hc : residualClosure H Mc = residual H) :
    ¬ (H0.subgroupOf Mc).map (residualPartnerAction Mc H hc) ≤
      centralizer ((((T : Subgroup G).subgroupOf Mc).map (residualPartnerAction Mc H hc)) :
        Set (MulAut (residual H ⧸ pCore 2 (residual H)))) := by
  rw [←source_residual_H_action_image s hc]
  let f := residualPartnerAction Mc H hc
  let A := (H1.subgroupOf Mc).map f
  let B := (H2.subgroupOf Mc).map f
  let D := (H0.subgroupOf Mc).map f
  let J := (H.subgroupOf Mc).map f
  intro hcent
  have hHM := original_partner_contains s
  have h1H := s.factors.first_le.trans s.factors.zero_le
  have h2H := s.factors.second_le.trans s.factors.zero_le
  obtain ⟨t,ht,_,hex⟩ := s.factors.exchanged
  let tM : Mc := ⟨t,hHM (s.outside.1.2 ht)⟩
  have htJ : f tM ∈ J := mem_map_of_mem f (s.outside.1.2 ht)
  have hfix (u : Mc) (hu : (u : G) ∈ H1) : f (tM⁻¹*u*tM) = f u := by
    have hc' := hcent (mem_map_of_mem f (s.factors.first_le hu)) (f tM) htJ
    simp only [map_mul,map_inv]
    rw [mul_assoc,←hc',inv_mul_cancel_left]
  have hBA : B ≤ A := by
    rintro y ⟨u,hu,rfl⟩
    obtain ⟨v,hv,he⟩ := hex.ge hu
    let vM : Mc := ⟨v,hHM (h1H hv)⟩
    have hev : tM⁻¹*vM*tM = u := by
      apply Subtype.ext
      change t⁻¹*v*(t⁻¹)⁻¹ = (u : G) at he
      change t⁻¹*v*t = (u : G)
      simpa only [inv_inv] using he
    refine ⟨vM,hv,?_⟩
    rw [←hev,hfix vM hv]
  have hj : D = A ⊔ B := by
    change (H0.subgroupOf Mc).map f = (H1.subgroupOf Mc).map f ⊔ (H2.subgroupOf Mc).map f
    have hsub : H0.subgroupOf Mc = H1.subgroupOf Mc ⊔ H2.subgroupOf Mc := by
      rw [←subgroupOf_sup (h1H.trans hHM) (h2H.trans hHM),s.factors.join_eq]
    rw [hsub,Subgroup.map_sup]
  have he : D = A := hj.trans (sup_eq_left.mpr hBA)
  have hdiv := action_subgroup_card_dvd s hc H1 h1H
  have hcard : Nat.card A = 4 := he ▸ source_residual_pair_action_card s hc
  change Nat.card A ∣ Nat.card (actorImage H H1) at hdiv
  rw [hcard,Nat.card_congr s.factors.first_model.some.toEquiv,DihedralGroup.nat_card] at hdiv
  norm_num at hdiv

include s in
/-- The original Sylow action on O²(H)/O₂(O²(H)) is genuinely dihedral of
order eight. This identifies the actual action image, before its matrix marking. -/
theorem source_residual_sylow_action_dihedral
    (hc : residualClosure H Mc = residual H) :
    Nonempty ((((T : Subgroup G).subgroupOf Mc).map (residualPartnerAction Mc H hc)) ≃*
      DihedralGroup 4) := by
  let f := residualPartnerAction Mc H hc
  let J := ((T : Subgroup G).subgroupOf Mc).map f
  let D := (H0.subgroupOf Mc).map f
  have hDJ : D ≤ J := by
    change (H0.subgroupOf Mc).map (residualPartnerAction Mc H hc) ≤
      ((T : Subgroup G).subgroupOf Mc).map (residualPartnerAction Mc H hc)
    rw [←source_residual_H_action_image s hc]
    exact map_mono (subgroupOf_mono Mc s.factors.zero_le)
  let := source_residual_pair_action_elementary s hc
  let : IsElementaryAbelian 2 (D.subgroupOf J) := IsElementaryAbelian.subgroupOf hDJ
  apply dihedral_eight_of_noncentral_elementary_four (source_residual_sylow_action_card s hc)
    (D.subgroupOf J)
  · rw [Nat.card_congr (subgroupOfEquivOfLe hDJ).toEquiv]
    exact source_residual_pair_action_card s hc
  · intro hz
    apply source_residual_pair_action_not_central s hc
    intro d hd j hj
    exact congrArg Subtype.val (mem_center_iff.mp (hz (show (⟨d,hDJ hd⟩ : J) ∈
      D.subgroupOf J from hd)) ⟨j,hj⟩)

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
