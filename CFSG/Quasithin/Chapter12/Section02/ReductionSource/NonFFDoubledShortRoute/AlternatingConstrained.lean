module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.AlternatingPushingUp
-- Reuse the internal cubic-section argument in this source family.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.AlternatingPushingUp
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpConstrained
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedRankOne
public import Theory.SpecificGroups.AlternatingSixNormalizer
-- Reuse the even-intersection and transposition calculations with a new section divisor.
import all Theory.SpecificGroups.AlternatingSixNormalizer
public import Theory.Alternating.Aut
public import Theory.SpecificGroups.Alternating.SixSubgroupObstructions

/-!
# Constrained alternating components on the original doubled orbit

The original intersection residual acts on the core-central quotient of
an escaping component with solvable kernel. Its perfect automorphism image
normalizes the full radical action, including outer automorphisms. A quotient
no larger than its A6 or A7 section would force this image to contain every
inner automorphism, contradicting the nontrivial radical action. In the A7
component quotient, the faithful permutation action and its two-normalizer
bounds give the same contradiction.

Together with the genuine C.2.7 star catalogue and the rank-two parabolic
exclusions, these arguments leave actual A8 and SL5(2) star markings in the
A6 row. The A7 row excludes A8 too: the remaining outer radical would be a
transposition, whose centralizer has order prime to seven. The final two
applications preserve the original reciprocal witness, full source orbit,
residual quotient maps, central kernels and relative normality in H.

The surviving SL5(2) parabolic actions, the A6/A8 module, ordinary components
and whole-orbit odd-normalizer control are still source obligations. This
module does not claim either alternating row or the doubled contradiction.
Source: Aschbacher--Smith C.2.7, C.4.5--8 and 4.4.6, printed pp.145--154,620,
refs/quasithin.pdf. The finite sieve uses the original B.5.1 classification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter4 Chapter4.Section04
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

private theorem constrained_actor_map
    {G : Type*} [Group G] [Finite G] {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H) :
    ∃ b : F →* coreCentralActorImage K (F.subgroupOf H),
      Function.Surjective b ∧ Group.IsSolvable b.ker := by
  let := hq
  have hs := h.normalized_span_eq hn
  have hFH : F ≤ H := h.component_le.trans h.local_le
  let A := F.subgroupOf H
  have hAK : A ≤ normalizer (K : Set H) := by
    simpa only [hs] using h.constrained_span_normalizes_intrinsic K hK hq
  let B := coreCentralActorImage K A
  let e : F ≃* A.subgroupOf (normalizer (K : Set H)) :=
    (subgroupOfEquivOfLe hFH).symm.trans (subgroupOfEquivOfLe hAK).symm
  let b : F →* B := ((normalizerCoreCentralAction K).subgroupMap
    (A.subgroupOf (normalizer (K : Set H)))).comp e.toMonoidHom
  have hb : Function.Surjective b :=
    ((normalizerCoreCentralAction K).subgroupMap_surjective _).comp e.surjective
  have hne : b ≠ 1 := by
    intro he
    apply h.constrained_span_action_nontrivial K hK hq hout
    rw [hs]
    apply bot_unique
    intro x hx
    obtain ⟨y,hy⟩ := hb ⟨x,hx⟩
    have hh := DFunLike.congr_fun he y
    rw [hy] at hh
    exact congrArg B.subtype hh
  have ht : (⊤ : Subgroup (F.subgroupOf M)).IsCComponent := by
    simpa using h.component.subgroupOf (le_refl (F.subgroupOf M))
  have htF : (⊤ : Subgroup F).IsCComponent := by
    simpa only [map_top_of_surjective (subgroupOfEquivOfLe h.component_le).toMonoidHom
      (subgroupOfEquivOfLe h.component_le).surjective] using
      ht.map_equiv (subgroupOfEquivOfLe h.component_le)
  have hk := kernel_le_solvableRadical_of_top_isCComponent htF b
    (fun ht => hne (MonoidHom.ker_eq_top_iff.mp ht))
  exact ⟨b,hb,Group.isSolvable_of_isSolvable_injective (inclusion_injective hk)⟩

private theorem no_constrained_small_central_quotient
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hS : ¬ Group.IsSolvable S) (π : F →* S) (hπ : Function.Surjective π)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (hc : Nat.card (coreCentralQuotient K) ≤ Nat.card S) : False := by
  let := hq
  let Q := coreCentralQuotient K
  let : IsSimpleGroup Q := hq.simple
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective
    (QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K)))
  let A := F.subgroupOf H
  let B := coreCentralActorImage K A
  let U := coreCentralActorImage K (R.subgroupOf H)
  obtain ⟨b,hb,hbk⟩ := constrained_actor_map h hn K hK hq hout
  let := hbk
  let : Group.IsPerfect F := (h.normalized_span_eq hn) ▸ h.span_perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective hb
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hz)).elim
  obtain ⟨f,hf,hconj⟩ := MulAut.perfect_subgroup_exists_inner_lift B hz
  have hd := SimpleSection.card_dvd_of_solvable_representation hS π hπ b
  have hB : Nat.card Q ≤ Nat.card B := hc.trans (Nat.le_of_dvd Nat.card_pos hd)
  have hsurj : Function.Surjective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hf,le_antisymm
      (Nat.card_le_card_of_injective f hf) hB⟩ |>.2
  have hi (x : Q) : MulAut.conj x ∈ B := by
    obtain ⟨a,rfl⟩ := hsurj x
    rw [hconj]
    exact a.property
  have hcore : pCore 2 Q = ⊥ := by
    rcases (inferInstance : (pCore 2 Q).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hp : IsPGroup 2 Q := IsPGroup.of_equiv pCore_isPGroup
        ((MulEquiv.subgroupCongr ht).trans topEquiv)
      let := hp.isNilpotent
      exact (Group.IsPerfect.not_isSolvable Q inferInstance).elim
  have hAR : A ≤ normalizer (R.subgroupOf H : Set H) := by
    intro a ha r
    exact h.span_normalizes_radical ((h.normalized_span_eq hn).symm ▸ ha) (r : G)
  have hBU := coreCentralActorImage_normalizes K A (R.subgroupOf H) hAR
  have hU : IsPGroup 2 U := h.isRadical.isPGroup.comap_subtype.map _
  let J := B ⊔ U
  have hj : pCore 2 J = ⊥ := automorphism_core_eq_bot 2
    (MulAut.conj_injective_of_center_eq_bot hz) hcore J (fun x => mem_sup_left (hi x))
  have hu : U ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes hU le_sup_right
    (sup_le hBU U.le_normalizer)
  unfold Subgroup.pCoreIn at hu
  rw [hj,Subgroup.map_bot] at hu
  exact h.constrained_radical_action_nontrivial K hK hq hout hfK (bot_unique hu)

private theorem constrained_permutation_actor_data
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hS : ¬ Group.IsSolvable S) (h3 : 2 ≤ primeRank 3 S) (h5 : 5 ∣ Nat.card S)
    (π : F →* S) (hπ : Function.Surjective π)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    {k : ℕ} (hk : 5 ≤ k) (hk6 : k ≠ 6)
    (e : coreCentralQuotient K ≃* alternatingGroup (Fin k)) :
    ∃ P N : Subgroup (Equiv.Perm (Fin k)), IsPGroup 2 P ∧ P ≠ ⊥ ∧
      N ≤ alternatingGroup (Fin k) ∧ N ≤ normalizer (P : Set _) ∧
      5 ∣ Nat.card N ∧ 2 ≤ primeRank 3 N ∧ Nat.card S ∣ Nat.card N := by
  let := hq
  let Q := coreCentralQuotient K
  let : IsSimpleGroup Q := hq.simple
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective
    (QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K)))
  let A := F.subgroupOf H
  let B := coreCentralActorImage K A
  let U := coreCentralActorImage K (R.subgroupOf H)
  obtain ⟨b,hb,hbk⟩ := constrained_actor_map h hn K hK hq hout
  let := hbk
  let : Group.IsPerfect F := (h.normalized_span_eq hn) ▸ h.span_perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective hb
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hz)).elim
  obtain ⟨f,hf,hconj⟩ := MulAut.perfect_subgroup_exists_inner_lift B hz
  let a : Equiv.Perm (Fin k) ≃* MulAut (alternatingGroup (Fin k)) :=
    MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj k hk hk6)
  let t := (MulAut.congr e).trans a.symm
  have ht (x : Q) : t (MulAut.conj x) = (e x : Equiv.Perm (Fin k)) := by
    apply a.injective
    change a (a.symm (MulAut.congr e (MulAut.conj x))) = _
    rw [a.apply_symm_apply]
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change (e (x * e.symm z * x⁻¹) : Equiv.Perm (Fin k)) = _
    simp only [map_mul,map_inv,e.apply_symm_apply,Subgroup.coe_mul,Subgroup.coe_inv]
    rfl
  let N := B.map t.toMonoidHom
  let P := U.map t.toMonoidHom
  have hN : N ≤ alternatingGroup (Fin k) := by
    rintro _ ⟨x,hx,rfl⟩
    change t (⟨x,hx⟩ : B).val ∈ _
    rw [←hconj ⟨x,hx⟩,ht]
    exact (e (f ⟨x,hx⟩)).property
  have hAR : A ≤ normalizer (R.subgroupOf H : Set H) := by
    intro x hx r
    exact h.span_normalizes_radical ((h.normalized_span_eq hn).symm ▸ hx) (r : G)
  have hBU := coreCentralActorImage_normalizes K A (R.subgroupOf H) hAR
  have hU : IsPGroup 2 U := h.isRadical.isPGroup.comap_subtype.map _
  have hP : P ≠ ⊥ := fun hp => h.constrained_radical_action_nontrivial K hK hq hout hfK
    ((U.map_eq_bot_iff_of_injective t.injective).mp hp)
  have h5B := h5.trans (SimpleSection.card_dvd_of_solvable_representation hS π hπ b)
  have h3B := cubic_rank_two_of_simple_section hS h3 π hπ b
  have h5N : 5 ∣ Nat.card N := by rwa [card_map_of_injective t.injective]
  have h3N : 2 ≤ primeRank 3 N := by
    rwa [←primeRank_equiv 3 (B.equivMapOfInjective t.toMonoidHom t.injective)]
  refine ⟨P,N,hU.map _,hP,hN,(map_mono hBU).trans (U.le_normalizer_map _),h5N,h3N,?_⟩
  rw [card_map_of_injective t.injective]
  exact SimpleSection.card_dvd_of_solvable_representation hS π hπ b

private theorem no_constrained_seven_central_quotient
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hS : ¬ Group.IsSolvable S) (h3 : 2 ≤ primeRank 3 S) (h5 : 5 ∣ Nat.card S)
    (π : F →* S) (hπ : Function.Surjective π)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : coreCentralQuotient K ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨P,N,hP,hne,hN,hnorm,h5N,h3N,_⟩ := constrained_permutation_actor_data
    h hn hS h3 h5 π hπ K hK hq hout hfK (by decide) (by decide) e
  exact Theory.SpecificGroups.AlternatingSixNormalizer.seven_no_normalized_two
    P N hP hne hN hnorm h5N h3N

private theorem no_constrained_eight_of_seven_section
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hS : ¬ Group.IsSolvable S) (h3 : 2 ≤ primeRank 3 S) (h5 : 5 ∣ Nat.card S)
    (h7 : 7 ∣ Nat.card S) (π : F →* S) (hπ : Function.Surjective π)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : coreCentralQuotient K ≃* alternatingGroup (Fin 8)) : False := by
  obtain ⟨P,N,hP,hne,hN,hnorm,h5N,_,hd⟩ := constrained_permutation_actor_data
    h hn hS h3 h5 π hπ K hK hq hout hfK (by decide) (by decide) e
  have h7N := h7.trans hd
  open Theory.SpecificGroups.AlternatingSixNormalizer in
  have he := even_intersection_eq_bot eight_five_not_dvd_normalizer P N hP hN hnorm h5N
  have hc := Theory.SpecificGroups.AlternatingSixNormalizer.card_two_of_even_intersection_bot P hne he
  obtain ⟨z,hz,_⟩ := (Nat.card_eq_two_iff' (1 : P)).mp hc
  have hz0 : (z : Equiv.Perm (Fin 8)) ≠ 1 := fun hh => hz (Subtype.ext hh)
  have hz2 : (z : Equiv.Perm (Fin 8)) ^ 2 = 1 := by
    have hh : z ^ Nat.card P = 1 := pow_card_eq_one'
    rw [hc] at hh
    exact congrArg Subtype.val hh
  have hNC : normalizer (P : Set _) ≤ centralizer ({(z : Equiv.Perm (Fin 8))} : Set _) :=
    (normalizer_le_centralizer_of_card_two P hc).trans
      (centralizer_le (Set.singleton_subset_iff.mpr z.property))
  have hs := Theory.SpecificGroups.AlternatingSixNormalizer.involution_isSwap_of_five_centralizer
    z hz2 hz0 (h5N.trans (card_dvd_of_le (hnorm.trans hNC)))
  have hd7 := h7N.trans (card_dvd_of_le (hnorm.trans hNC))
  rw [Equiv.Perm.nat_card_centralizer,Equiv.Perm.isSwap_iff_cycleType.mp hs] at hd7
  norm_num [Nat.factorial] at hd7

private theorem constrained_binary_remainder
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hS : ¬ Group.IsSolvable S) (h3 : 2 ≤ primeRank 3 S) (h5 : 5 ∣ Nat.card S)
    (hsize : 360 ≤ Nat.card S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : F →* S) (hπ : Function.Surjective π)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    Nonempty (starImage (K.map H.subtype) R (K.map H.subtype) ≃* alternatingGroup (Fin 8)) ∨
    Nonempty (starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2)) := by
  let X := starImage (K.map H.subtype) R (K.map H.subtype)
  let ec := h.constrained_star_central_equiv K hK hq hout hfK
  have hd := (constrained_normalized_simple_order_dvd h hn hS π hπ K hK hq hout).trans
    ((Nat.card_congr ec.toEquiv).symm ▸ (center X).card_quotient_dvd_card)
  have hfive := h5.trans hd
  have hm := ChapterC.C27Source.star_model_from_source
    (h.constrained_source_input K hK hq hout hfK)
  cases hm with
  | linearTwo E e => exact (h.no_constrained_component_star_linear_two K hK hq hout hfK E e).elim
  | linearThree E e =>
    by_cases hE : 1 < E.degree
    · exact (no_constrained_normalized_linear_three h hn hS hexp π hπ K hK hq hout hfK E hE e).elim
    · have hdeg : E.degree = 1 := by have := E.degree_pos; omega
      rw [Nat.card_congr e.toEquiv] at hfive
      have hc := (center SL(3,E.Carrier)).index_mul_card
      rw [Atlas.ExceptionalSupport.card_sl_center] at hc
      change Nat.card PSL(3,E.Carrier) * Nat.gcd 3 (Nat.card E.Carrier - 1) = _ at hc
      rw [←hc,Matrix.PSL3.LinearThree.card_projective_mul_scalar,E.card_eq,hdeg] at hfive
      norm_num at hfive
  | symplectic E hE e =>
    exact (no_constrained_normalized_symplectic h hn hS hexp π hπ K hK hq hout hfK e (by
      rw [E.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ E.degree))).elim
  | g2 E hE e =>
    exact (no_constrained_normalized_g2 h hn hS hexp π hπ K hK hq hout hfK e (by
      rw [E.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ E.degree))).elim
  | g2DerivedTwo e =>
    rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hfive
    norm_num at hfive
  | alternating n hn' e =>
    rcases hn' with rfl | rfl | rfl | rfl
    · exact (h.no_constrained_component_star_alternating_five K hK hq hout hfK e).elim
    · apply (no_constrained_small_central_quotient h hn hS π hπ K hK hq hout hfK ?_).elim
      let a := ec.trans (centerQuotientCongr e)
      have hc := (center (alternatingGroup (Fin 6))).card_quotient_dvd_card
      rw [←Nat.card_congr a.toEquiv] at hc
      have hh := Nat.le_of_dvd (Nat.card_pos) hc
      rw [nat_card_alternatingGroup] at hh
      norm_num [Nat.factorial] at hh
      omega
    · let a := ec.trans ((centerQuotientCongr e).trans
        ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot
          (by norm_num : 4 ≤ Nat.card (Fin 7)))).trans QuotientGroup.quotientBot))
      exact (no_constrained_seven_central_quotient h hn hS h3 h5 π hπ K hK hq hout hfK a).elim
    · exact Or.inl ⟨e⟩
  | linearFiveTwo e => exact Or.inr ⟨e⟩
  | tripleSix ez e =>
    apply (no_constrained_small_central_quotient h hn hS π hπ K hK hq hout hfK ?_).elim
    rw [Nat.card_congr (ec.trans e).toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
    exact hsize

private theorem alternating_not_two_exponent {n : ℕ} (hn : n = 6 ∨ n = 7) :
    ¬ ∀ P : Subgroup (alternatingGroup (Fin n)), IsPGroup 2 P → ∀ x : P, x ^ 2 = 1 := by
  intro h
  rcases hn with rfl | rfl
  · obtain ⟨P,hP,a,b,_,_,hab⟩ :=
      alternatingGroup.SixSubgroupObstructions.exists_two_subgroup_noncommuting_involutions
    exact hab (Commute.of_orderOf_dvd_two (fun g => orderOf_dvd_of_pow_eq_one (h P hP g)) a b)
  · let x : alternatingGroup (Fin 7) :=
      ⟨(Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3) * Equiv.swap 4 5, by change Equiv.Perm.sign _ = 1; decide⟩
    have h4 : x ^ 4 = 1 := by decide
    have h2 : x ^ 2 ≠ 1 := by decide
    have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 2) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one h4)
    exact h2 (congrArg Subtype.val (h _ hp ⟨x,mem_zpowers x⟩))

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- In both original alternating reciprocal rows, every constrained escaping
component has an actual A8 or SL5(2) star marking. All other C.2.7 rows are
excluded through the original residual and its full core-central action. -/
theorem sourceOrbit_alternating_witness_constrained_binary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin n)) Y)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    K.Normal ∧
      (Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
        alternatingGroup (Fin 8)) ∨
       Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃* SL(5,ZMod 2))) := by
  refine ⟨D.sourceOrbit_alternating_witness_constrained_normal h hn σ hmodel hw K hK hq hout hfK,?_⟩
  obtain ⟨m⟩ := hmodel
  let e := (D.componentCentralQuotientEquiv h.quasisimple).trans
    ((centerQuotientCongr m.groupEquiv).trans
      ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot
        (by simp only [Nat.card_eq_fintype_card,Fintype.card_fin]; omega :
          4 ≤ Nat.card (Fin n)))).trans QuotientGroup.quotientBot))
  let := h.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (alternatingGroup (Fin n)) := e.symm.isSimpleGroup
  let : Group.IsPerfect (alternatingGroup (Fin n)) := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  rcases hw with ⟨_,_,_,_,_,_,hc,_,hNF,_,_,⟨c,_⟩,_⟩
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let π : F →* alternatingGroup (Fin n) := e.toMonoidHom.comp
    ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp
      (c.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))))
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (c.surjective.comp (QuotientGroup.mk'_surjective _)))
  apply constrained_binary_remainder hc
    ((normal_subgroupOf_iff_le_normalizer hc.component_le).mp hNF)
    (Group.IsPerfect.not_isSolvable _) (alternatingGroup.TwoThreeCycles.two_le_primeRank (by omega))
    _ _ (alternating_not_two_exponent hn) π hπ K hK hq hout hfK
  · rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]
  · rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]

/-- The A7 residual also excludes the A8 star row: an outer radical would
be generated by a transposition, whose centralizer has no factor seven.
Thus the original constrained branch retains only the actual SL5(2) marking. -/
theorem sourceOrbit_seven_witness_constrained_linearFive
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    K.Normal ∧ Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃* SL(5,ZMod 2)) := by
  obtain ⟨hKn,hcases⟩ := D.sourceOrbit_alternating_witness_constrained_binary h
    (Or.inr rfl) σ hmodel hw K hK hq hout hfK
  refine ⟨hKn,?_⟩
  rcases hcases with ha | ha
  · exfalso
    obtain ⟨a⟩ := ha
    obtain ⟨m⟩ := hmodel
    let e := (D.componentCentralQuotientEquiv h.quasisimple).trans
      ((centerQuotientCongr m.groupEquiv).trans
        ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot
          (by norm_num : 4 ≤ Nat.card (Fin 7)))).trans QuotientGroup.quotientBot))
    let := h.quasisimple
    let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
    let : IsSimpleGroup (alternatingGroup (Fin 7)) := e.symm.isSimpleGroup
    let : Group.IsPerfect (alternatingGroup (Fin 7)) := Group.IsPerfect.ofSurjective
      (f := e.toMonoidHom) e.surjective
    rcases hw with ⟨_,_,_,_,_,_,hc,_,hNF,_,_,⟨c,_⟩,_⟩
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let π : F →* alternatingGroup (Fin 7) := e.toMonoidHom.comp
      ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp
        (c.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))))
    have hπ : Function.Surjective π := e.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp (c.surjective.comp (QuotientGroup.mk'_surjective _)))
    let ec := (hc.constrained_star_central_equiv K hK hq hout hfK).trans
      ((centerQuotientCongr a).trans
        ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot
          (by norm_num : 4 ≤ Nat.card (Fin 8)))).trans QuotientGroup.quotientBot))
    exact no_constrained_eight_of_seven_section hc
      ((normal_subgroupOf_iff_le_normalizer hc.component_le).mp hNF)
      (Group.IsPerfect.not_isSolvable _)
      (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide))
      (by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial])
      (by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]) π hπ K hK hq hout hfK ec
  · exact ha

/-- The original A7 reciprocal consumer with the constrained sieve discharged.
The same witness retains the full source orbit, residual cores and fixed subgroup. -/
theorem sourceOrbit_seven_reciprocal_reduced_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ J H W : Subgroup G, Witness L V A J H W ∧
      ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
        (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
      let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      D.sourceOrbit ≤ J.pCoreIn 2 ∧ D.sourceOrbit ≤ F.pCoreIn 2 ∧
      D.sourceOrbit = ⁅D.sourceOrbit,F⁆ ∧
      D.sourceOrbit ⊓ centralizer (F : Set G) = ⊥ ∧
      ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧ K.Normal ∧
        (IsComponent H K ∨ (generalizedFitting K = pCore 2 K ∧
          Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃* SL(5,ZMod 2)))) := by
  obtain ⟨J,H,W,hw,he,hWJ,hWF,hcomm,hfix,K,hK,hq,hout,hKn,hcases⟩ :=
    D.sourceOrbit_seven_reciprocal_normal_component h hmany hnon σ hmodel A hA ho hnot
  refine ⟨J,H,W,hw,he,hWJ,hWF,hcomm,hfix,K,hK,hq,hout,hKn,?_⟩
  rcases hcases with hoK | hf
  · exact Or.inl hoK
  · exact Or.inr ⟨hf,(D.sourceOrbit_seven_witness_constrained_linearFive h σ hmodel hw K hK hq hout hf).2⟩

/-- The original A6 reciprocal consumer with the constrained sieve discharged.
The same witness retains the full source orbit, residual cores and fixed subgroup. -/
theorem sourceOrbit_six_reciprocal_reduced_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ J H W : Subgroup G, Witness L V A J H W ∧
      ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
        (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
      let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      D.sourceOrbit ≤ J.pCoreIn 2 ∧ D.sourceOrbit ≤ F.pCoreIn 2 ∧
      D.sourceOrbit = ⁅D.sourceOrbit,F⁆ ∧
      D.sourceOrbit ⊓ centralizer (F : Set G) = ⊥ ∧
      ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧ K.Normal ∧
        (IsComponent H K ∨ (generalizedFitting K = pCore 2 K ∧
          (Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
            alternatingGroup (Fin 8)) ∨
          Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃* SL(5,ZMod 2))))) := by
  obtain ⟨J,H,W,hw,he,hWJ,hWF,hcomm,hfix,K,hK,hq,hout,hKn,hcases⟩ :=
    D.sourceOrbit_six_reciprocal_normal_component h hmany hnon hmodel A hA ho hnot
  refine ⟨J,H,W,hw,he,hWJ,hWF,hcomm,hfix,K,hK,hq,hout,hKn,?_⟩
  rcases hcases with hoK | hf
  · exact Or.inl hoK
  · exact Or.inr ⟨hf,(D.sourceOrbit_alternating_witness_constrained_binary h (Or.inl rfl)
      (alternatingNatural 6) hmodel hw K hK hq hout hf).2⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
