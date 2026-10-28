module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceWitnessRanks
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceLinearTorus
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceGeometricTorus
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceWitnessRanks
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectedTorus
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectedTorusRanks
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectedTorusBounds

/-!
# Tori of the actual Hermitian geometric witnesses

The quotient and conjugation maps lift the same odd torus, retaining its order.
The natural-sum calculation identifies its fixed subgroup in the linear row.
The central intersection gives the rank identity and the global r-bound;
Hermitian plane geometry then excludes the intermediate and endpoint degrees.
These arguments require no relation with the ambient E-generation parameter.
The companion saturation and Chapter 12 extensions finish the higher-field
exclusion on the original action. Half-degree one remains in the endpoint proof.

Source: Aschbacher--Smith E.2.14 and 8.2.2--4, pp.226--228,714--716,
refs/quasithin.pdf. The proofs adapt the existing selected-torus calculations
using only the geometric clauses already constructed for actual witnesses.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ParabolicTorus
open scoped Matrix MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource.GeometricSelected
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {H T M V I : Subgroup G} [IsElementaryAbelian 2 V]
  {k : ℕ} {i : I} {S : Sylow 2 I}

omit [Finite G] in
private theorem star_model (s : GeometricSelected H T M V I k i S) :
    RankOneAlternative (Star M I) (starImage M I M) k := by
  have h := s.models.map (coreQuotientEquiv M I s.core_eq).symm
  have hm : (coreImage I M).map (coreQuotientEquiv M I s.core_eq).symm.toMonoidHom =
      starImage M I M := by
    rw [← starImage_map_coreQuotientEquiv M I M s.core_eq,map_map]
    have he : (coreQuotientEquiv M I s.core_eq).symm.toMonoidHom.comp
        (coreQuotientEquiv M I s.core_eq).toMonoidHom = MonoidHom.id _ := by
      ext x
      exact (coreQuotientEquiv M I s.core_eq).symm_apply_apply x
    rw [he,map_id]
  rwa [hm] at h

theorem star_centralizer_two (s : GeometricSelected H T M V I k i S) (hk : 1 < k) :
    IsPGroup 2 ↥(starImage M I M ⊓ centralizer (starImage M I V : Set (Star M I))) := by
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  let : IsElementaryAbelian 2 (V.subgroupOf I) := IsElementaryAbelian.subgroupOf hVI
  let : IsElementaryAbelian 2 (starImage M I V) :=
    IsElementaryAbelian.map (QuotientGroup.mk' (localCore M I))
  have hne : starImage M I V ≠ ⊥ := by
    intro hz
    have he := starImage_map_coreQuotientEquiv M I V s.core_eq
    rw [hz,Subgroup.map_bot] at he
    have hr := s.rank_eq
    rw [← he,Representation.BinaryOffender.rank_bot] at hr
    omega
  obtain ⟨z,hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hzval : z.val ≠ 1 := fun he => hz (Subtype.ext he)
  have hz2 : orderOf z.val = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z.val z.property) hzval
  have hc := rankOne_involution_centralizer_two (star_model s) hk z.val hz2
  apply hc.to_le
  intro a ha
  exact mem_centralizer_singleton_iff.mpr (ha.2 z.val z.property).symm

theorem action_kernel_two (s : GeometricSelected H T M V I k i S) (hk : 1 < k) :
    IsPGroup 2 (selectedActionMap M I V (s.normalizer_eq ▸ inf_le_right)).ker :=
  selectedActionMap_ker_two M I V _ s.core_eq (star_centralizer_two s hk)

theorem exists_torus (s : GeometricSelected H T M V I k i S) (hk : 1 < k) :
    ∃ y : ↥(M ⊓ I), orderOf y = 2^k-1 ∧
      orderOf (selectedStarMap M I y) = 2^k-1 ∧
      orderOf (selectedActionMap M I V (s.normalizer_eq ▸ inf_le_right) y) = 2^k-1 := by
  obtain ⟨x,hx,hxo⟩ := rankOne_exists_torus_element (star_model s) hk
  let f : ↥(M ⊓ I) →* starImage M I M :=
    (selectedStarMap M I).codRestrict _ (fun y => mem_map_of_mem _ y.property.1)
  have hf : Function.Surjective f := by
    rintro ⟨x,v,hv,rfl⟩
    exact ⟨⟨v.val,hv,v.property⟩,rfl⟩
  have hker : IsPGroup 2 f.ker := by
    dsimp only [f]
    rw [MonoidHom.ker_codRestrict]
    exact selectedStarMap_ker_two M I s.core_eq
  have ho : Odd (2^k-1) := Nat.Even.sub_odd (Nat.one_le_pow k 2 (by decide))
    (Nat.even_pow.mpr ⟨by decide,by omega⟩) odd_one
  obtain ⟨y,hy,hyo⟩ := odd_element_lift f hf hker ⟨x,hx⟩ (by rwa [← Subgroup.orderOf_coe,hxo])
  have hyorder : orderOf y = 2^k-1 := hyo.trans (by rw [← Subgroup.orderOf_coe,hxo])
  refine ⟨y,hyorder,?_,?_⟩
  · have he : selectedStarMap M I y = x := congrArg Subtype.val hy
    rw [he,hxo]
  · rw [(selectedActionMap M I V (s.normalizer_eq ▸ inf_le_right)).orderOf_map_eq_of_coprime_of_isPGroup_ker
      (action_kernel_two s hk) y (hyorder ▸ ho.coprime_two_left),hyorder]

theorem normalizes_actor (s : GeometricSelected H T M V I k i S) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    inducedAutomizer V (M ⊓ I) ≤ normalizer (inducedAutomizer V A : Set (Automizer V)) := by
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  let B := V ⊓ (pCore 2 I).map I.subtype
  let P := (TwoConjugate.P (V.subgroupOf I) (M.subgroupOf I) i⁻¹).map I.subtype
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hPeq : P = B ⊔ A := by
    dsimp only [P,TwoConjugate.P]
    rw [Subgroup.map_sup,selected_actor_image I M V hVI S i s.twoConjugate,
      s.twoConjugate.B_eq_twoCore_inf,Subgroup.map_inf _ _ _ I.subtype_injective,
      map_subgroupOf_eq_of_le hVI,inf_comm]
  have hPM : P ≤ M := by
    rintro _ ⟨p,hp,rfl⟩
    apply (M.subgroupOf I).normalCore_le
    change p ∈ localCore M I
    rw [s.core_eq]
    exact s.twoConjugate.P_le_twoCore hp
  have hPNV : P ≤ normalizer (V : Set G) :=
    (le_inf hPM (map_subtype_le _)).trans (s.normalizer_eq ▸ inf_le_right)
  have hNP : I ≤ normalizer (P : Set G) := by
    let J := TwoConjugate.P (V.subgroupOf I) (M.subgroupOf I) i⁻¹
    let : J.Normal := s.twoConjugate.core_geometry.1
    have hh := J.le_normalizer_map I.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
  have hBN : B ≤ normalizer (V : Set G) := le_sup_left.trans (hPeq ▸ hPNV)
  have hAN : A ≤ normalizer (V : Set G) := le_sup_right.trans (hPeq ▸ hPNV)
  have hb : inducedAutomizer V B = ⊥ := (inducedAutomizer_eq_bot_iff hBN).mpr
    (inf_le_left.trans V.le_centralizer)
  have he : inducedAutomizer V P = inducedAutomizer V A := by
    rw [hPeq,inducedAutomizer,subgroupOf_sup hBN hAN,Subgroup.map_sup]
    change inducedAutomizer V B ⊔ inducedAutomizer V A = _
    rw [hb,bot_sup_eq]
  change inducedAutomizer V (M ⊓ I) ≤ normalizer (inducedAutomizer V A : Set (Automizer V))
  rw [← he]
  have hn : M ⊓ I ≤ normalizer (P : Set G) := inf_le_right.trans hNP
  have hn' : (M ⊓ I).subgroupOf (normalizer (V : Set G)) ≤
      normalizer (P.subgroupOf (normalizer (V : Set G)) : Set (normalizer (V : Set G))) := by
    rw [← subgroupOf_normalizer_eq hPNV]
    exact comap_mono hn
  exact (map_mono hn').trans (le_normalizer_map V.normalizerMonoidHom.rangeRestrict)

theorem exists_automizer_torus (s : GeometricSelected H T M V I k i S) (hk : 1 < k) :
    ∃ (y : ↥(M ⊓ I)) (x : Automizer V),
      x = (selectedActionMap M I V (s.normalizer_eq ▸ inf_le_right) y).val ∧
      orderOf y = 2^k-1 ∧ orderOf (selectedStarMap M I y) = 2^k-1 ∧
      x ∈ inducedAutomizer V (M ⊓ I) ∧ orderOf x = 2^k-1 := by
  obtain ⟨y,hy,hq,ha⟩ := exists_torus s hk
  exact ⟨y,_,rfl,hy,hq,(selectedActionMap M I V _ y).property,
    (Subgroup.orderOf_coe _).trans ha⟩

theorem linear_odd_centralizer
    (s : GeometricSelected H T M V I k i S) (hk : 1 < k)
    (ξ : (I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField k))
    (y : ↥(M ⊓ I))
    (ho : Odd (orderOf (selectedStarMap M I y)))
    (hne : selectedStarMap M I y ≠ 1) :
    V ⊓ centralizer ({y.val} : Set G) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  let e := ((QuotientGroup.quotientMulEquivOfEq s.core_eq).trans ξ).trans
    (Theory.PSL2.sl2QuotientEquiv (BinaryGaloisField k)).symm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (localCore M I))
  let R := S.mapSurjective (f := q)
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨hMN,hVS,hMS⟩ := linear_markings s ξ
  let x : I := ⟨y.val,y.property.2⟩
  have hx : q x = e (selectedStarMap M I y) := rfl
  have hodd : Odd (orderOf (q x)) := by
    rw [hx]
    change Odd (orderOf (e.toMonoidHom (selectedStarMap M I y)))
    rwa [orderOf_injective e.toMonoidHom e.injective]
  have hxne : q x ≠ 1 := by
    rw [hx]
    exact fun he => hne (e.map_eq_one_iff.mp he)
  have hc := s.twoConjugate.linear_pair_odd_centralizer hMN k (by omega)
    (GaloisField.card 2 k (by omega)) e R hVS hMS x hodd hxne
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  rw [←selected_intersection_image I V hVI i,←hc]
  apply le_antisymm
  · intro v hv
    refine ⟨⟨v,hVI hv.1⟩,⟨hv.1,?_⟩,rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (show Commute (⟨v,hVI hv.1⟩ : I) x from
        Subtype.ext ((mem_centralizer_singleton_iff.mp hv.2)))
  · rintro _ ⟨v,hv,rfl⟩
    exact ⟨hv.1,mem_centralizer_singleton_iff.mpr
      (congrArg I.subtype (mem_centralizer_singleton_iff.mp hv.2))⟩

theorem linear_exists_torus_fixed
    (s : GeometricSelected H T M V I k i S) (hk : 1 < k)
    (ξ : (I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField k)) :
    ∃ (y : ↥(M ⊓ I)) (x : Automizer V),
      x = (selectedActionMap M I V (s.normalizer_eq ▸ inf_le_right) y).val ∧
      orderOf y = 2^k-1 ∧ orderOf (selectedStarMap M I y) = 2^k-1 ∧
      x ∈ inducedAutomizer V (M ⊓ I) ∧ orderOf x = 2^k-1 ∧
      automizerFixedGroup V (zpowers x) =
        V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  obtain ⟨y,x,hxy,hy,hq,hx,ho⟩ := exists_automizer_torus s hk
  have hodd : Odd (orderOf (selectedStarMap M I y)) := by
    rw [hq]
    exact Nat.Even.sub_odd (Nat.one_le_pow k 2 (by decide))
      (Nat.even_pow.mpr ⟨by decide,by omega⟩) odd_one
  have hne : selectedStarMap M I y ≠ 1 := by
    intro he
    rw [he,orderOf_one] at hq
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    omega
  have hc := linear_odd_centralizer s hk ξ y hodd hne
  have himage := selected_lift_action_image M I V (s.normalizer_eq ▸ inf_le_right) (zpowers y)
  rw [MonoidHom.map_zpowers,MonoidHom.map_zpowers] at himage
  have hnorm : (zpowers y).map (M ⊓ I).subtype ≤ normalizer (V : Set G) :=
    (map_subtype_le _).trans (s.normalizer_eq ▸ inf_le_right)
  have hfix := automizerFixedGroup_induced V ((zpowers y).map (M ⊓ I).subtype) hnorm
  rw [←himage] at hfix
  change automizerFixedGroup V (zpowers (selectedActionMap M I V _ y).val) = _ at hfix
  rw [←hxy,MonoidHom.map_zpowers] at hfix
  have hcz : centralizer (zpowers y.val : Set G) = centralizer ({y.val} : Set G) := by
    rw [zpowers_eq_closure,centralizer_closure]
  change automizerFixedGroup V (zpowers x) = V ⊓ centralizer (zpowers y.val : Set G) at hfix
  rw [hcz] at hfix
  exact ⟨y,x,hxy,hy,hq,hx,ho,hfix.trans hc⟩

theorem actor_rank_identity (s : GeometricSelected H T M V I k i S) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    rank (V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) + k +
      rank (inducedAutomizer V A) = rank V := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let Z := V ⊓ W
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hAN : A ≤ normalizer (V : Set G) := actor_normalizes s
  have hker : A ⊓ centralizer (V : Set G) = Z :=
    selected_actor_kernel I M V hVI S i s.twoConjugate
  have hr := rank_inducedAutomizer V A hAN
  rw [hker] at hr
  have hZA : Z ≤ A := hker ▸ inf_le_left
  have hc : subgroupCorank W A = k := by
    rw [conjugate_core_corank I V i.val i.property,
      ← quotient_rank_eq_core_corank I V hVI]
    exact s.rank_eq
  have hs := offender_corank_add hZA (show A ≤ W from inf_le_left)
  have hz := offender_corank_add (W := W) (A := Z) bot_le inf_le_right
  have hz' : rank W = subgroupCorank W Z + rank Z := by
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hz
  have hw : rank W = rank V := by
    dsimp only [W,rank]
    rw [card_map_of_injective (MulAut.conj i.val⁻¹).injective]
  change rank Z + k + rank (inducedAutomizer V A) = rank V
  omega

theorem fixed_rank_gt_three_mul
    (s : GeometricSelected H T M V I k i S) (n : ℕ)
    (hdim : rank V = 9*n) (hrank : primeRank 2 (Automizer V) ≤ 4*n)
    (hkn : k < 2*n) (x : Automizer V)
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) :
    3*n < Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) (zpowers x)) := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := offender_elementary_of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (actor_normalizes s)
  have hb := (offender_rank_le_primeRank (inducedAutomizer V A)).trans hrank
  have hi := actor_rank_identity s
  change rank (V ⊓ W) + k + rank (inducedAutomizer V A) = rank V at hi
  have hf := rank_automizerFixedGroup (V := V) (zpowers x)
  rw [hfixed] at hf
  change rank (V ⊓ W) = _ at hf
  omega

omit [Finite G] in
theorem not_normalizes (s : GeometricSelected H T M V I k i S) :
    ¬ I ≤ normalizer (V : Set G) := by
  intro hn
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  let : (V.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hn
  have hcore : V.subgroupOf I ≤ pCore 2 I :=
    le_sSup ⟨inferInstance, (IsElementaryAbelian.isPGroup 2 V).comap_subtype⟩
  have he : coreImage I V = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [QuotientGroup.ker_mk'] using hcore
  have hr := s.rank_eq
  rw [he, Representation.BinaryOffender.rank_bot] at hr
  have hk := s.positive
  omega

theorem globalR_le_rank_sum (s : GeometricSelected H T M V I k i S) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    globalR V ≤ ((k + rank (inducedAutomizer V A) : ℕ) : ℕ∞) := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let Z := V ⊓ W
  have hIC : I ≤ centralizer (Z : Set G) := by
    intro a ha z hz
    obtain ⟨z',hz',he⟩ := s.intersection_central hz
    have hc := mem_center_iff.mp hz' (⟨a,ha⟩ : I)
    have hc' : a * I.subtype z' = I.subtype z' * a := congrArg I.subtype hc
    rw [he] at hc'
    exact hc'.symm
  have hr := globalR_le_corank (V := V) (U := Z) inf_le_left
    (fun hc => not_normalizes s (hIC.trans hc))
  have he := actor_rank_identity s
  have hz := offender_corank_add (W := V) (A := Z) bot_le inf_le_left
  have hz' : subgroupCorank V Z + rank Z = rank V := by
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hz.symm
  have heq : subgroupCorank V Z = k +
      rank (inducedAutomizer V (W ⊓ (pCore 2 I).map I.subtype)) := by
    change rank Z + k + rank (inducedAutomizer V (W ⊓ (pCore 2 I).map I.subtype)) = rank V at he
    omega
  rwa [heq] at hr

theorem actor_fixedCodim_ge_five_mul
    (s : GeometricSelected H T M V I k i S) (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V) (hk : k < 2*n) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    5*n ≤ fixedCodim (automizerRepresentation V) (inducedAutomizer V A) ∧
      5*n ≤ k + rank (inducedAutomizer V A) := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let Z := V ⊓ W
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (actor_normalizes s)
  let : IsElementaryAbelian 2 ((inducedAutomizer V A).map j) := IsElementaryAbelian.map j
  have hsum : 4*n ≤ k + rank (inducedAutomizer V A) :=
    ENat.natCast_le_natCast.mp (hr.trans (globalR_le_rank_sum s))
  have hlarge : 2*n < rank ((inducedAutomizer V A).map j) := by
    rw [rank_map_injective j hj]
    omega
  have hb := overgroup_fixedCodim_of_rank_gt_two_mul n (binaryNormalizer n) le_rfl
    ((inducedAutomizer V A).map j) hlarge
  rw [← fixedCodim_map_equivariant (automizerRepresentation V)
    (overgroupAction n (binaryNormalizer n)) j e he] at hb
  refine ⟨hb,?_⟩
  have hZA : Z ≤ V ⊓ centralizer (A : Set G) :=
    le_inf inf_le_left (inf_le_right.trans (W.le_centralizer.trans (centralizer_le inf_le_left)))
  have hc := offender_corank_add hZA (show V ⊓ centralizer (A : Set G) ≤ V from inf_le_left)
  have hz := offender_corank_add (W := V) (A := Z) bot_le inf_le_left
  have hi := actor_rank_identity s
  rw [fixedCodim_inducedAutomizer V A (actor_normalizes s)] at hb
  have hz' : subgroupCorank V Z + rank Z = rank V := by
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hz.symm
  change rank Z + k + rank (inducedAutomizer V A) = rank V at hi
  change 5*n ≤ k + rank (inducedAutomizer V A)
  omega

theorem fixedSpace_le_actor
    (s : GeometricSelected H T M V I k i S) (x : Automizer V)
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) :
    fixedSpace (automizerRepresentation V) (zpowers x) ≤
      fixedSpace (automizerRepresentation V) (inducedAutomizer V
        (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  intro v hv
  apply (mem_fixedSpace_inducedAutomizer V A (actor_normalizes s) v).mpr
  have hvG : v.toMul.val ∈ automizerFixedGroup V (zpowers x) := ⟨v.toMul,hv,rfl⟩
  rw [hfixed] at hvG
  exact (centralizer_le (show A ≤ W from inf_le_left)) (W.le_centralizer hvG.2)

theorem not_intermediate_of_fixed_plane
    (s : GeometricSelected H T M V I k i S) (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V)
    (x : Automizer V) (ho : orderOf x = 2^k-1)
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hnk : n < k) (hkn : k < 2*n) : False := by
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (actor_normalizes s)
  have hrank : primeRank 2 (Automizer V) ≤ 4*n :=
    (Theory.GroupTheory.primeRank_le_of_injective 2 j hj).trans
      (OuterRank.normalizer_twoRank_le n (normalizerCoverage n) ⟨FieldSections.centralizerEquiv n⟩)
  have hdim : rank V = 9*n := by
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
  have hm : Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation V) (zpowers x)) =
      Module.finrank (ZMod 2)
        (fixedSpace (overgroupAction n (binaryNormalizer n)) (zpowers (j x))) := by
    rw [←MonoidHom.map_zpowers,
      ←fixedSpace_map_equivariant (automizerRepresentation V)
        (overgroupAction n (binaryNormalizer n)) j e he,LinearEquiv.finrank_map_eq]
  have hlarge := fixed_rank_gt_three_mul s n hdim hrank hkn x hfixed
  have hodd : Odd (orderOf x) := by
    rw [ho]
    exact Nat.Even.sub_odd (Nat.one_le_pow k 2 (by decide))
      (Nat.even_pow.mpr ⟨by decide,by omega⟩) odd_one
  have hoj : Odd (orderOf (j x)) := by rwa [orderOf_injective j hj]
  obtain ⟨hl,_⟩ := largeOddFixedSpaceLinearity n (binaryNormalizer n) (j x)
    (j x).property hoj (hm ▸ hlarge)
  let f := (binaryNormalizer n).subtype.comp j
  let B := (inducedAutomizer V A).map f
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  have hsum := (actor_fixedCodim_ge_five_mul s n e j hj he hr hkn).2
  change 5*n ≤ k + rank (inducedAutomizer V A) at hsum
  have hfi : Function.Injective f := (binaryNormalizer n).subtype_injective.comp hj
  have hBr : 2*n+1 < rank B := by
    rw [rank_map_injective f hfi]
    have hn := NeZero.pos n
    omega
  have hBN : B ≤ binaryNormalizer n := by
    rintro _ ⟨b,hb,rfl⟩
    exact (j b).property
  have hBL := Chapter7.NormalizedSource.NonMathieuHermitian.large_elementary_le_image n B hBN hBr
  have hmap (D : Subgroup (Automizer V)) :
      (fixedSpace (automizerRepresentation V) D).map e.toLinearMap =
        fixedSpace (UnipotentRadicals.ambientAction n) (D.map f) :=
    fixedSpace_map_equivariant _ _ f e he D
  have hX : (zpowers x).map f = zpowers (j x).val := MonoidHom.map_zpowers f x
  have hBX : 3*n < Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (j x).val)) := by
    rw [←hX,←hmap,LinearEquiv.finrank_map_eq]
    exact hlarge
  have hle : fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (j x).val) ≤
      fixedSpace (UnipotentRadicals.ambientAction n) B := by
    rw [←hX,←hmap,←hmap]
    exact Submodule.map_mono (fixedSpace_le_actor s x hfixed)
  obtain ⟨g,hg⟩ := OddExponent.mem_congruenceImage_of_odd_of_isFixedFieldLinear n
    (j x).val (j x).property (by rwa [Subgroup.orderOf_coe]) hl
  have hd := odd_order_dvd_of_large_fixed_inside_inner_actor n B hBL (by omega) g
    (by rwa [hg,Subgroup.orderOf_coe]) (by rwa [hg]) (by rwa [hg])
  rw [hg,Subgroup.orderOf_coe,orderOf_injective j hj,ho] at hd
  have hkdiv := (Offenders.pow_sub_one_dvd_pow_sub_one_iff_dvd (by omega : 0 < k)).mp hd
  obtain ⟨d,hd⟩ := hkdiv
  have hlo : 2 ≤ d := by nlinarith
  nlinarith

private theorem endpoint_not_maximal_actor
    (s : GeometricSelected H T M V I k i S) (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (x : Automizer V) (ho : Odd (orderOf x))
    (hx : x ∈ inducedAutomizer V (M ⊓ I))
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (ha : rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) = 4*n)
    (hxf : Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation V) (zpowers x)) = 3*n) : False := by
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  let f := (binaryNormalizer n).subtype.comp j
  have hfi : Function.Injective f := (binaryNormalizer n).subtype_injective.comp hj
  let B := (inducedAutomizer V A).map f
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (actor_normalizes s)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  have hB : B ≤ binaryNormalizer n := by
    rintro _ ⟨a,ha,rfl⟩
    exact (j a).property
  have hBr : rank B = 4*n := (rank_map_injective f hfi _).trans ha
  have hBL := Chapter7.NormalizedSource.NonMathieuHermitian.large_elementary_le_image n B hB
    (by rw [hBr]; have hn := NeZero.pos n; omega)
  have hmap (D : Subgroup (Automizer V)) :
      (fixedSpace (automizerRepresentation V) D).map e.toLinearMap =
        fixedSpace (UnipotentRadicals.ambientAction n) (D.map f) :=
    fixedSpace_map_equivariant _ _ f e he D
  have hX : (zpowers x).map f = zpowers (j x).val := MonoidHom.map_zpowers f x
  have hBX : Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (j x).val)) = 3*n := by
    rw [←hX,←hmap,LinearEquiv.finrank_map_eq]
    exact hxf
  have hle : fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (j x).val) ≤
      fixedSpace (UnipotentRadicals.ambientAction n) B := by
    rw [←hX,←hmap,←hmap]
    exact Submodule.map_mono (fixedSpace_le_actor s x hfixed)
  obtain ⟨c,hc | hc⟩ := UnipotentRadicals.maximal_elementary_conjugate n B hBL hBr
  · have hd := (fixedSpaceConjEquiv (UnipotentRadicals.ambientAction n) B
        (binaryActionHom n c)).finrank_eq
    rw [hc,UnipotentRadicals.finrank_point_fixed] at hd
    have hh := Submodule.finrank_mono hle
    rw [hBX,hd] at hh
    have hn := NeZero.pos n
    omega
  · have hBA := (fixedSpaceConjEquiv (UnipotentRadicals.ambientAction n) B
        (binaryActionHom n c)).finrank_eq
    rw [hc,UnipotentRadicals.finrank_plane_fixed] at hBA
    have hnorm : (j x).val ∈ normalizer (B : Set (BinaryAut n)) :=
      (inducedAutomizer V A).le_normalizer_map f
        (mem_map_of_mem f (normalizes_actor s hx))
    have hodd : Odd (orderOf (j x).val) := by
      rwa [Subgroup.orderOf_coe,orderOf_injective j hj]
    have hlin := linear_of_large_fixed_inside_actor n B hBL hBA (j x).val
      (j x).property hodd hnorm hle (by rw [hBX]; have hn := NeZero.pos n; omega)
    obtain ⟨g,hg⟩ := OddExponent.mem_congruenceImage_of_odd_of_isFixedFieldLinear n
      (j x).val (j x).property hodd hlin
    have hgo := OddExponent.odd_orderOf_of_odd_binaryCongruence n g (hg.symm ▸ hodd)
    exact conjugate_plane_no_fixed_rank_three_mul n B c hc g hgo
      (hg.symm ▸ hnorm) (hg.symm ▸ hle) (hg.symm ▸ hBX)

/-- The proved lower actor rank forces a maximal actor at k = 2n.
Its torus would fix rank 3n in the plane, contradicting the minus form. -/
theorem not_endpoint
    (s : GeometricSelected H T M V I k i S) (n : ℕ) [NeZero n] (hkn : k = 2*n)
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (x : Automizer V) (ho : orderOf x = 2^k-1)
    (hx : x ∈ inducedAutomizer V (M ⊓ I))
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) : False := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (actor_normalizes s)
  have hu : rank (inducedAutomizer V A) ≤ 4*n :=
    (offender_rank_le_primeRank _).trans ((_root_.primeRank_le_of_injective 2 j hj).trans
      (OuterRank.normalizer_twoRank_le n (normalizerCoverage n) ⟨FieldSections.centralizerEquiv n⟩))
  have hl := s.actor_rank_ge_twice_parameter
  change 2*k ≤ rank (inducedAutomizer V A) at hl
  have ha : rank (inducedAutomizer V A) = 4*n := by omega
  have hdim : rank V = 9*n := by
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
  have hid := s.actor_rank_identity
  change rank (V ⊓ W) + k + rank (inducedAutomizer V A) = rank V at hid
  have hz := rank_automizerFixedGroup (V := V) (zpowers x)
  rw [hfixed] at hz
  change rank (V ⊓ W) = _ at hz
  have hxf : Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation V) (zpowers x)) = 3*n := by omega
  have hodd : Odd (orderOf x) := by
    rw [ho]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (even_two.pow_of_ne_zero (by have hp := s.positive; omega)) odd_one
  exact endpoint_not_maximal_actor s n e j hj he x hodd hx hfixed ha hxf

end CFSG.Quasithin.Chapter8.Section02.HermitianSource.GeometricSelected
