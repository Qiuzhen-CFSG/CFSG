module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.OddRefinement.SmallActors
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.Setup
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalAction
public import Theory.ElementaryAbelian.RankOneImageCriterion

/-!
# Small original stabilizer images in a component pair

The local core-quotient conjugation image is the actual actor used by E.1.5.
Its kernel is a two-group and lies in the local solvable radical, so image
order at most two gives quotient rank at most one. If tau moves the component,
its full orbit makes the normalized actor faithful. If the actor itself moves
the component, its stabilizer is faithful and an image of order at most two
forces the whole actor to have order at most four. The already constructed
norm-diagonal member then has degree one and escapes the actual unique maximal.
Finally the prime-field automorphism rank bounds this same stabilizer image
by four. No universal automorphism-rank-one or generic actor-transfer assertion
is made. Source: Aschbacher–Smith E.1.2, E.1.11 and E.2.2, pp.210,213–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds.Paired.PrimeSharp
variable {G : Type*} [Group G] [Finite G]

private theorem core_center {K : Subgroup G} (hK : IsComponent G K) [IsSimpleGroup K] :
    pCore 2 K = ⊥ ∧ center (K ⧸ pCore 2 K) = ⊥ := by
  let := hK.2
  have hz : center K = ⊥ := by
    rcases (inferInstance : (center K).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp h)).elim
  have hc : pCore 2 K = ⊥ := bot_unique ((IsQuasisimple.pCore_le_center 2).trans hz.le)
  refine ⟨hc,?_⟩
  let e : (K ⧸ pCore 2 K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  apply bot_unique
  intro x hx
  have he : e x ∈ center K := (centerCongr e ⟨x,hx⟩).property
  rw [hz,mem_bot] at he
  exact mem_bot.mpr (e.injective (he.trans e.map_one.symm))

theorem quotient_rank_one_of_action_card (K U A : Subgroup G)
    (hn : U ≤ normalizer K) (hU : IsPGroup 2 U)
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    [IsElementaryAbelian 2 A] (hAJ : A ≤ K ⊔ U)
    (hc : Nat.card ((A.subgroupOf (K ⊔ U)).map (pCoreJoinAction 2 hn)) ≤ 2) :
    Group.rank ((A.subgroupOf (K ⊔ U)).map
      (QuotientGroup.mk' (solvableRadical (K ⊔ U : Subgroup G)))) ≤ 1 := by
  let J := K ⊔ U
  let B := A.subgroupOf J
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAJ
  apply (IsElementaryAbelian.rank_quotient_image_le_one_iff_card_le_twice_intersection B _).mpr
  have hprod := IsElementaryAbelian.card_inf_ker_mul_card_map B (pCoreJoinAction 2 hn)
  have hk : (pCoreJoinAction 2 hn).ker ≤ solvableRadical J := by
    rw [pCoreJoinAction_kernel 2 hn hU hz]
    let := (pCore_isPGroup (p:=2) (G:=J)).isNilpotent
    exact le_solvableRadical _ inferInstance inferInstance
  have hb := card_le_of_le (inf_le_inf_left B hk)
  change Nat.card (B.map (pCoreJoinAction 2 hn)) ≤ 2 at hc
  nlinarith

theorem normalized_simple_member_one (T : Sylow 2 G) {K A : Subgroup G}
    (hK : IsComponent G K) [IsSimpleGroup K]
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (ht : tau (T : Subgroup G) A ≤ normalizer K)
    (hne : ¬ A ≤ centralizer (K : Set G))
    (hc : Nat.card ((A.subgroupOf (ChiefOrbit.localGroup T K)).map
      (pCoreJoinAction 2 (show ChiefOrbit.stabilizer T K ≤ normalizer K from inf_le_right))) ≤ 2) :
    IsEMemberAt 1 (T : Subgroup G) A (K ⊔ tau (T : Subgroup G) A) := by
  have h := ChiefOrbit.NormalSimpleTau.component_tau_join_member T hK le_rfl hAT ht hne
  refine ⟨h.1,?_⟩
  rcases h.1.2.2.2.2.2 with ho | he
  · exact .inl ⟨ho,(by obtain ⟨p,_,_,_,_,_,hr⟩ := ho; omega)⟩
  · refine .inr ⟨he,quotient_rank_one_of_action_card K _ A ht
      (T.isPGroup'.to_le (tau_le _ _)) (core_center hK).2
      ((le_sup_left.trans (sup_pCore_le_tau T A hAT)).trans le_sup_right) ?_⟩
    have hAl : A ≤ ChiefOrbit.localGroup T K :=
      (le_sup_left.trans (sup_pCore_le_tau T A hAT)).trans
        ((le_inf (tau_le _ _) ht).trans le_sup_right)
    have heq : (A.subgroupOf (K ⊔ tau (T : Subgroup G) A)).map (pCoreJoinAction 2 ht) =
        (A.subgroupOf (ChiefOrbit.localGroup T K)).map
          (pCoreJoinAction 2 (show ChiefOrbit.stabilizer T K ≤ normalizer K from inf_le_right)) := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact ⟨⟨x,hAl hx⟩,hx,rfl⟩
      · rintro ⟨x,hx,rfl⟩
        exact ⟨⟨x,(le_sup_left.trans (sup_pCore_le_tau T A hAT)).trans le_sup_right hx⟩,hx,rfl⟩
    rwa [heq]

theorem local_actor_card_of_full_orbit (T : Sylow 2 G) {K A E : Subgroup G}
    (hK : IsComponent G K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hcore : pCore 2 G = ⊥)
    (hAT : A ≤ (T : Subgroup G))
    (hEA : E ≤ centralizer (A : Set G))
    (ho : componentOrbit K E = componentOrbit K (T : Subgroup G)) :
    Nat.card (A.subgroupOf (ChiefOrbit.localGroup T K)) =
      Nat.card ((A.subgroupOf (ChiefOrbit.localGroup T K)).map
        (pCoreJoinAction 2 (show ChiefOrbit.stabilizer T K ≤ normalizer K from inf_le_right))) := by
  let V := A ⊓ centralizer (K : Set G)
  have hEV : E ≤ centralizer (V : Set G) := hEA.trans (centralizer_le inf_le_left)
  have hEC : componentOrbit K E ≤ centralizer (V : Set G) :=
    iSup_conjugates_le_of_le_normalizer K E _ (le_centralizer_iff.mp inf_le_right)
      (hEV.trans (centralizer (V : Set G)).le_normalizer)
  have hv : V = ⊥ := by
    apply le_bot_iff.mp
    rw [←hcore,←hK.sylow_centralizer_orbit_eq_pCore T hgen,←ho]
    exact le_inf (inf_le_left.trans hAT) (le_centralizer_iff.mp hEC)
  let B := A.subgroupOf (ChiefOrbit.localGroup T K)
  let ρ := pCoreJoinAction 2 (show ChiefOrbit.stabilizer T K ≤ normalizer K from inf_le_right)
  let f := ρ.comp B.subtype
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro b hb
    have ha : K.normalizerMonoidHom
        (inclusion (sup_le K.le_normalizer (show ChiefOrbit.stabilizer T K ≤ normalizer K from inf_le_right)) b.val) = 1 :=
      (quotientAut_injective_of_pCore_eq_bot K (core_center hK).1)
        (by
          change (quotientAut (pCore 2 K)) (K.normalizerMonoidHom
            (inclusion (sup_le K.le_normalizer (show ChiefOrbit.stabilizer T K ≤ normalizer K from inf_le_right)) b.val)) = 1 at hb
          simpa only [map_one] using hb)
    have hc : ((b.val : ChiefOrbit.localGroup T K) : G) ∈ centralizer (K : Set G) := by
      change _ ∈ K.normalizerMonoidHom.ker at ha
      rw [normalizerMonoidHom_ker] at ha
      exact ha
    have he : ((b.val : ChiefOrbit.localGroup T K) : G) = 1 := by
      have hh : ((b.val : ChiefOrbit.localGroup T K) : G) ∈ V := ⟨b.property,hc⟩
      simpa only [hv,mem_bot] using hh
    exact Subtype.ext (Subtype.ext he)
  let e : B ≃* B.map ρ := MulEquiv.ofBijective (ρ.subgroupMap B)
    ⟨fun x y h => hf (congrArg Subtype.val h),ρ.subgroupMap_surjective B⟩
  exact Nat.card_congr e.toEquiv

theorem moving_card_le_four_of_action_card (T : Sylow 2 G) {K A : Subgroup G}
    (hK : IsComponent G K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hcore : pCore 2 G = ⊥)
    (hlayer : pResidual 2 G = componentLayer G)
    (hindex : (normalizer (K : Set G)).index = 2)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hm : ¬ A ≤ normalizer K)
    (hc : Nat.card ((A.subgroupOf (ChiefOrbit.localGroup T K)).map
      (pCoreJoinAction 2 (show ChiefOrbit.stabilizer T K ≤ normalizer K from inf_le_right))) ≤ 2) :
    Nat.card A ≤ 4 := by
  have hAC : A ≤ centralizer (A : Set G) := by
    intro a ha b hb
    let : CommGroup A := IsMulCommutative.instCommGroup
    exact congrArg Subtype.val (mul_comm (⟨b,hb⟩ : A) ⟨a,ha⟩)
  have hTmove : ¬ (T : Subgroup G) ≤ normalizer K := fun h => hm (hAT.trans h)
  have ho := (moved_pair_orbit_eq_residual T hK hgen hlayer hindex hm).trans
    (moved_pair_orbit_eq_residual T hK hgen hlayer hindex hTmove).symm
  have hB := local_actor_card_of_full_orbit T hK hgen hcore hAT hAC ho
  have hsmall : Nat.card (A ⊓ normalizer K : Subgroup G) ≤ 2 := by
    rw [←ChiefOrbit.map_local_actor_eq_stabilizer_intersection T K A hAT,
      card_map_of_injective (ChiefOrbit.localGroup T K).subtype_injective]
    exact hB.trans_le hc
  let N := normalizer (K : Set G)
  let : N.Normal := normal_of_index_eq_two hindex
  have hd := relIndex_dvd_index_of_normal (H:=N) (K:=A)
  have hi : (N.subgroupOf A).index ≤ 2 := Nat.le_of_dvd (by decide) (hindex ▸ hd)
  have hcN : Nat.card (N.subgroupOf A) ≤ 2 := by
    have h := card_map_of_injective (K:=N.subgroupOf A) A.subtype_injective
    rw [subgroupOf_map_subtype,inf_comm] at h
    exact h.symm.trans_le hsmall
  have he := (N.subgroupOf A).index_mul_card
  nlinarith


theorem small_action_member_escape
    (hG : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable G) (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K A : Subgroup G} (hK : IsComponent G K)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hn : ¬K.Normal)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hAC : ¬A ≤ centralizer (K : Set G))
    (hc : Nat.card ((A.subgroupOf (ChiefOrbit.localGroup T K)).map
      (pCoreJoinAction 2 (show ChiefOrbit.stabilizer T K ≤ normalizer K from inf_le_right))) ≤ 2) :
    ∃ X : Subgroup G, IsEMemberAt 1 (T : Subgroup G) A X ∧
      ¬X ≤ ChapterB.minimalParabolicMax T hP := by
  have hrad : solvableRadical G = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  have hcore := SimpleSocle.pCore_eq_bot hrad 2
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup K := isSimpleGroup_of_isQuasisimple_of_solvableRadical_eq_bot hrad hK.1
  have hi : (normalizer (K : Set G)).index = 2 := by
    rcases component_normal_or_pair hG T hK hgen with h | ⟨t,_,_,_,_,_,_,hi⟩
    · exact (hn h.1).elim
    · exact hi
  have hl := residual_eq_layer T hK hgen
  have hKM : ¬K ≤ ChapterB.minimalParabolicMax T hP := by
    intro h
    exact (ChapterB.minimalParabolicMax_spec T hP).1.ne_top
      (top_unique (hgen ▸ sup_le h (ChapterB.minimalParabolicMax_spec T hP).2))
  by_cases hAN : A ≤ normalizer K
  · refine ⟨K ⊔ tau (T : Subgroup G) A,?_,fun hx => hKM (le_sup_left.trans hx)⟩
    by_cases ht : tau (T : Subgroup G) A ≤ normalizer K
    · exact normalized_simple_member_one T hK hAT ht hAC hc
    · have ho := moved_pair_orbit_eq_residual T hK hgen hl hi ht
      have hT : ¬(T : Subgroup G) ≤ normalizer K := fun h => ht ((tau_le _ _).trans h)
      have hoT := moved_pair_orbit_eq_residual T hK hgen hl hi hT
      have htc : tau (T : Subgroup G) A ≤ centralizer (A : Set G) := by
        intro t ht a ha
        have hh := (mem_centralizerModulo_iff.mp ht).2 a ha
        rw [hcore,mem_bot,commutatorElement_eq_one_iff_mul_comm] at hh
        exact hh
      have hAl : A ≤ ChiefOrbit.localGroup T K := (le_inf hAT hAN).trans le_sup_right
      have hcard : Nat.card A ≤ 2 := by
        rw [←Nat.card_congr (subgroupOfEquivOfLe hAl).toEquiv]
        exact (local_actor_card_of_full_orbit T hK hgen hcore hAT htc (ho.trans hoT.symm)).trans_le hc
      have hra : Group.rank A ≤ 1 := IsElementaryAbelian.rank_le_of_card_le (p:=2) A hcard
      have hcomm : K = ⁅K,A⁆ := by
        rcases simple_subnormal_commutator_dichotomy K A hK.1 with hb | he
        · exact (hAC (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))).elim
        · rw [he]
          apply le_antisymm (le_componentOrbit K A)
          exact iSup_le fun a => (mem_normalizer_iff_map_conj_eq.mp (hAN a.property)).le
      exact ChiefOrbit.tau_join_member_of_full_orbit T hK hrad hl hAT ho (.inl hcomm) hra
  · exact OddRefinement.exists_small_moving_member_escape hG T hP hs hJ hK hgen hn hAT hAN
      (moving_card_le_four_of_action_card T hK hgen hcore hl hi hAT hAN hc)

theorem prime_action_card_dichotomy (T : Sylow 2 G) {K A : Subgroup G}
    (hK : IsComponent G K) [IsSimpleGroup K]
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hm : ClassicalGroup.IsPSL K 2 p)
    [IsElementaryAbelian 2 A] :
    let B := (A.subgroupOf (ChiefOrbit.localGroup T K)).map
      (pCoreJoinAction 2 (show ChiefOrbit.stabilizer T K ≤ normalizer K from inf_le_right))
    Nat.card B ≤ 2 ∨ Nat.card B = 4 := by
  let V := A.subgroupOf (ChiefOrbit.localGroup T K)
  let : IsElementaryAbelian 2 V := {
    toIsMulCommutative := Subgroup.subgroupOf_isMulCommutative _ A
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a =>
      Subtype.ext (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A:=A) _ a.property))) }
  let B := V.map (pCoreJoinAction 2 (show ChiefOrbit.stabilizer T K ≤ normalizer K from inf_le_right))
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map (A:=V)
    (pCoreJoinAction 2 (show ChiefOrbit.stabilizer T K ≤ normalizer K from inf_le_right))
  have hc : pCore 2 K = ⊥ := (core_center hK).1
  let e : (K ⧸ pCore 2 K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hr : primeRank 2 (MulAut (K ⧸ pCore 2 K)) ≤ 2 := by
    rw [primeRank_equiv 2 (MulAut.congr e)]
    obtain ⟨F,_,_,hF,⟨ek⟩⟩ := hm
    rw [primeRank_equiv 2 (MulAut.congr ek)]
    exact Theory.PSL2.prime_card_automorphism_two_rank F hF hp
  have hb : Nat.card B ≤ 4 := by
    let : CommGroup B := IsMulCommutative.instCommGroup
    have hd := card_dvd_exponent_pow_rank' B
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 B))
    have hrb := (B.rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 _)).trans hr
    exact (Nat.le_of_dvd (by positivity) hd).trans
      (by simpa using pow_le_pow_right' (by decide : 1 ≤ 2) hrb)
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
  change Nat.card B ≤ 2 ∨ Nat.card B = 4
  rw [hk] at hb ⊢
  have hkle : k ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
  interval_cases k <;> norm_num

end CFSG.Quasithin.ChapterE.Structure.NumericalBounds.Paired.PrimeSharp
