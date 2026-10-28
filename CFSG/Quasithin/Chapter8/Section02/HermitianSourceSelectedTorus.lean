module
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Selection
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.ActionTorus
public import Theory.SpecificGroups.PSL2.RankOneRoots
public import Theory.SpecificGroups.Suzuki.RankOneRoots
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Constructing the selected torus and its original automizer image

The actual rank-one quotient has a split torus of order 2^k−1 for k > 1.
Lift its generator through the two-group quotient kernel. The independent
action kernel is also a two-group: the nonzero elementary generator image
contains an involution, whose centralizer is a two-group in the marked
PSL₂ or Suzuki model. The lift therefore keeps exactly the same odd order
in the original automizer. No identification of the two kernels is made.

The normal subgroup P = AB in the selected I has the same automizer image
as A, since B ≤ V. Hence N_I(V) normalizes the actual actor image, although
A itself need not be normal in I. The final conditional consumer applies
E.2.14(9) to this constructed torus and identifies its fixed subgroup with
the original V ∩ V^i, without a model-centralizer callback.

The earlier E.2.14(9) source clause remains explicit. Selection and the
Hermitian endpoint and field-four exclusions are not proved here; final
assembly remains with the original Hermitian exclusion task.

Source: Aschbacher–Smith E.2.10(1), E.2.14(9), and 8.2.2(8)–8.2.4,
printed pp.222, 227 and 715–716 (1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped IsMulCommutative
open Subgroup Representation.BinaryOffender
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic.Construction

private theorem rankOne_involution_centralizer_two
    {X : Type*} [Group X] [Finite X] {N : Subgroup X} {k : ℕ}
    (h : RankOneAlternative X N k) (hk : 1 < k) (z : X) (hz : orderOf z = 2) :
    IsPGroup 2 (centralizer ({z} : Set X)) := by
  have transport {Y : Type} [Group Y] (e : X ≃* Y)
      (hc : IsPGroup 2 (centralizer ({e z} : Set Y))) :
      IsPGroup 2 (centralizer ({z} : Set X)) := by
    apply (hc.comap_of_injective e.toMonoidHom e.injective).to_le
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((show Commute x z from mem_centralizer_singleton_iff.mp hx).map e).eq
  rcases h with ⟨_,e,_⟩ | ⟨m,hm,_,e,_⟩ | ⟨he,_⟩
  · obtain ⟨_,_,_,_,_,hc⟩ := Theory.PSL2.involution_root_geometry (e z)
      ((orderOf_injective e.toMonoidHom e.injective z).trans hz)
    exact transport e hc
  · obtain ⟨_,_,_,_,_,hc⟩ := suzuki_involution_root_geometry m hm (e z)
      ((orderOf_injective e.toMonoidHom e.injective z).trans hz)
    exact transport e hc
  · omega

private theorem rankOne_exists_torus_element
    {X : Type*} [Group X] {N : Subgroup X} {k : ℕ}
    (h : RankOneAlternative X N k) (hk : 1 < k) :
    ∃ x : X, x ∈ N ∧ orderOf x = 2^k-1 := by
  have transport {Y : Type} [Group Y] (e : X ≃* Y) (B : Subgroup Y)
      (he : N.map e.toMonoidHom = B) (y : Y) (hy : y ∈ B)
      (ho : orderOf y = 2^k-1) : ∃ x : X, x ∈ N ∧ orderOf x = 2^k-1 := by
    have hy' : y ∈ N.map e.toMonoidHom := he ▸ hy
    obtain ⟨x,hx,hxy⟩ := hy'
    refine ⟨x,hx,?_⟩
    rw [← orderOf_injective e.toMonoidHom e.injective x, hxy]
    exact ho
  rcases h with ⟨_,e,he⟩ | ⟨m,hm,hk',e,he⟩ | ⟨he,_⟩
  · let F := BinaryGaloisField k
    let f := (pi F).comp (torHom F)
    have hf : Function.Injective f := pi_injective.comp torHom_injective
    obtain ⟨a,ha⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic Fˣ)
    apply transport e (PBorel F) he (f a)
    · apply PTorus_le_PBorel
      exact mem_map_of_mem (pi F) (by rw [Torus_eq_range]; exact ⟨a,rfl⟩)
    · rw [orderOf_injective f hf,ha,Nat.card_units]
      congr 1
      exact GaloisField.card 2 k (by omega)
  · let : IsCyclic (SuzukiSplitTorus m) := suzukiSplitTorus_isCyclic m hm
    obtain ⟨a,ha⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic (SuzukiSplitTorus m))
    apply transport e (SuzukiBorelSubgroup m) he a.val
    · rw [suzukiBorelSubgroup_eq_sup]
      exact (show SuzukiSplitTorus m ≤ SuzukiRootSubgroup m ⊔ SuzukiSplitTorus m from le_sup_right) a.property
    · rw [Subgroup.orderOf_coe,ha,suzukiSplitTorus_card m hm,hk']
  · omega

private theorem odd_element_lift
    {P X : Type*} [Group P] [Finite P] [Group X] [Finite X]
    (f : P →* X) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker)
    (x : X) (ho : Odd (orderOf x)) :
    ∃ y : P, f y = x ∧ orderOf y = orderOf x := by
  obtain ⟨D,hD,hi,_,_⟩ := f.exists_odd_subgroup_lift hf hker (zpowers x)
    (by rwa [Nat.card_zpowers])
  obtain ⟨y,hy,hxy⟩ := show x ∈ D.map f from hD ▸ mem_zpowers x
  refine ⟨y,hxy,?_⟩
  have hh := orderOf_injective (f.comp D.subtype) hi (⟨y,hy⟩ : D)
  change orderOf (f y) = orderOf (⟨y,hy⟩ : D) at hh
  rw [← Subgroup.orderOf_coe, hxy] at hh
  exact hh.symm

variable {G : Type*} [Group G] [Finite G]
  {H T M V I : Subgroup G} [IsElementaryAbelian 2 V]
  {k : ℕ} {i : I} {S : Sylow 2 I}

private theorem selected_star_model (s : Selected H T M V I k i S) :
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

/-- The centralizer of the original generator image is a two-group in
the actual selected quotient. This discharges the model input used to
compare its torus with the automizer torus. -/
theorem selected_star_centralizer_two (s : Selected H T M V I k i S) (hk : 1 < k) :
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
  have hc := rankOne_involution_centralizer_two (selected_star_model s) hk z.val hz2
  apply hc.to_le
  intro a ha
  exact mem_centralizer_singleton_iff.mpr (ha.2 z.val z.property).symm

/-- The action kernel is a two-group, using the same quotient and
generator as the selected pair. No model-centralizer premise remains. -/
theorem selected_action_kernel_two (s : Selected H T M V I k i S) (hk : 1 < k) :
    IsPGroup 2 (selectedActionMap M I V (s.normalizer_eq ▸ inf_le_right)).ker :=
  selectedActionMap_ker_two M I V _ s.core_eq (selected_star_centralizer_two s hk)

/-- Construct the cyclic torus on the original selected automizer. The
lift and the quotient have the same odd order, and the actual action
retains that order through its independently proved two-group kernel. -/
theorem selected_exists_torus (s : Selected H T M V I k i S) (hk : 1 < k) :
    ∃ y : ↥(M ⊓ I), orderOf y = 2^k-1 ∧
      orderOf (selectedStarMap M I y) = 2^k-1 ∧
      orderOf (selectedActionMap M I V (s.normalizer_eq ▸ inf_le_right) y) = 2^k-1 := by
  obtain ⟨x,hx,hxo⟩ := rankOne_exists_torus_element (selected_star_model s) hk
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
      (selected_action_kernel_two s hk) y (hyorder ▸ ho.coprime_two_left),hyorder]

/-- The actual normalizer of V in I normalizes the selected actor's
image. The normal subgroup P = AB has that same image because B ≤ V
acts trivially; no normality of A inside I is asserted. -/
theorem selected_normalizes_actor (s : Selected H T M V I k i S) :
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

/-- The constructed torus in the actual automizer, retaining its lift in
M ∩ I and its exact order in the original star quotient. -/
theorem selected_exists_automizer_torus (s : Selected H T M V I k i S) (hk : 1 < k) :
    ∃ (y : ↥(M ⊓ I)) (x : Automizer V),
      x = (selectedActionMap M I V (s.normalizer_eq ▸ inf_le_right) y).val ∧
      orderOf y = 2^k-1 ∧ orderOf (selectedStarMap M I y) = 2^k-1 ∧
      x ∈ inducedAutomizer V (M ⊓ I) ∧ orderOf x = 2^k-1 := by
  obtain ⟨y,hy,hq,ha⟩ := selected_exists_torus s hk
  exact ⟨y,_,rfl,hy,hq,(selectedActionMap M I V _ y).property,
    (Subgroup.orderOf_coe _).trans ha⟩

/-- E.2.14(9) applies to the actual selected torus, with its existence,
quotient marking and two-group centralizer all discharged. The earlier
source torus theorem is the sole additional action input. -/
theorem selected_exists_torus_fixed
    (K : GroupClass) (e14 : E214TorusClause (G := G) K)
    (h28 : HypothesisE28 K H T M V) (hchar : HasCharacteristicTwo H)
    (hTI : LocalTI H M V)
    (s : Selected H T M V I k i S) (hk : 1 < k) :
    ∃ (y : ↥(M ⊓ I)) (x : Automizer V),
      x = (selectedActionMap M I V (s.normalizer_eq ▸ inf_le_right) y).val ∧
      orderOf y = 2^k-1 ∧ orderOf (selectedStarMap M I y) = 2^k-1 ∧
      x ∈ inducedAutomizer V (M ⊓ I) ∧ orderOf x = 2^k-1 ∧
      automizerFixedGroup V (zpowers x) =
        V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  obtain ⟨y,x,hxy,hy,hq,hx,ho⟩ := selected_exists_automizer_torus s hk
  let a : inducedAutomizer V (M ⊓ I) := ⟨x,hx⟩
  have hc : Nat.card (zpowers a) = 2^k-1 := by
    rw [Nat.card_zpowers,← Subgroup.orderOf_coe]
    exact ho
  have hfixed := selected_torus_fixed K e14 H T M V I k h28 s.family hchar hTI
    i s.generate s.intersection_ne_bot s.core_eq (s.normalizer_eq ▸ inf_le_right)
    (selected_star_model s) (selected_star_centralizer_two s hk) hk (zpowers a) hc
  rw [MonoidHom.map_zpowers] at hfixed
  exact ⟨y,x,hxy,hy,hq,hx,ho,hfixed⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
