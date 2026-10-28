module
public import CFSG.Quasithin.Chapter14.Section02.ResidualSylow
public import Theory.GroupTheory.Commutator.PrimeImage
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.SylowSmallCoreQuotient

/-!
# The original moving residual and its symmetric-three extension

For an actual subgroup R of T containing O₂(Y), the original action map
has cubic Y-image and two-group kernel on Y. If Y does not normalize R,
prime-image commutator generation gives Y=[Y,R]. The nontrivial two-image
of R then fills S₃ together with Y, and the exact kernel calculation
recognizes (YR)/O₂(YR). The same original Sylow intersects YR in R.
The normal-source consumer supplies the nonnormality input using 3.1.1.

Source: Aschbacher--Smith 14.2.14 and the surrounding F.1.1 verification,
printed p.984.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_residual_actor_movement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (R : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hQR : (sourceResidual M Mc).pCoreIn 2 ≤ R)
    (hnot : ¬sourceResidual M Mc ≤ normalizer (R : Set G)) :
    let Y := sourceResidual M Mc
    Y = ⁅Y,R⁆ ∧ Nonempty (((Y ⊔ R : Subgroup G) ⧸ pCore 2 (Y ⊔ R : Subgroup G)) ≃*
      Equiv.Perm (Fin 3)) := by
  let Y := sourceResidual M Mc
  let YM := Y.subgroupOf M
  let RM := R.subgroupOf M
  let C := (centralizer (localModule T M : Set G)).subgroupOf M
  let f := e.toMonoidHom.comp (QuotientGroup.mk' C)
  have hYM : Y ≤ M := sourceResidual_le _ _
  have hRM : R ≤ M := hRT.trans hM.1.2
  have hk : f.ker = C := by
    ext x
    change e (QuotientGroup.mk x) = 1 ↔ x ∈ C
    rw [←e.map_one,e.injective.eq_iff,QuotientGroup.eq_one_iff]
  obtain ⟨_,_,_,_,heY,hcore,_⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hYc : Nat.card (YM.map f) = 3 := by
    change Nat.card (YM.map (e.toMonoidHom.comp (QuotientGroup.mk' C))) = 3
    rw [←Subgroup.map_map,Nat.card_congr
      ((YM.map (QuotientGroup.mk' C)).equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm]
    rw [Nat.card_congr heY.some.toEquiv]
    exact Nat.card_zmod 3
  have hYker : YM ⊓ f.ker = (Y.pCoreIn 2).subgroupOf M := by
    rw [hk,hcore]
    rfl
  have hpY : IsPPerfect 2 YM :=
    (residualY_isPPerfect M Mc).of_surjective (subgroupOfEquivOfLe hYM).symm.toMonoidHom
      (subgroupOfEquivOfLe hYM).symm.surjective
  let : YM.Normal := residualY_normal M Mc
  have hkerp : IsPGroup 2 (YM ⊓ f.ker : Subgroup M) := by
    rw [hYker]
    exact (isPGroup_pCoreIn 2 Y).comap_subtype
  have hmoveM : YM = ⁅YM,RM⁆ := by
    rcases eq_commutator_or_normalizes_of_prime_image YM RM f hpY le_normalizer_of_normal
      hkerp (hYker ▸ subgroupOf_mono M hQR) (by rw [hYc]; exact Nat.prime_three) with hh | hh
    · exact hh
    · apply (hnot _).elim
      have hm := (map_mono (f := M.subtype) hh).trans (RM.le_normalizer_map M.subtype)
      simpa only [YM,RM,map_subgroupOf_eq_of_le hYM,map_subgroupOf_eq_of_le hRM] using hm
  have hmove : Y = ⁅Y,R⁆ := by
    have hm := congrArg (Subgroup.map M.subtype) hmoveM
    simpa only [map_commutator,YM,RM,map_subgroupOf_eq_of_le hYM,map_subgroupOf_eq_of_le hRM] using hm
  have hRp : IsPGroup 2 RM := (T.isPGroup'.to_le hRT).comap_subtype
  have hRne : RM.map f ≠ ⊥ := by
    intro hz
    have hm := congrArg (Subgroup.map f) hmoveM
    rw [map_commutator,hz,commutator_bot_right] at hm
    have hc : Nat.card (YM.map f) = 1 := hm ▸ card_bot
    omega
  have hRc : Nat.card (RM.map f) = 2 := by
    have hd : Nat.card (RM.map f) ∣ 2*3 := by
      simpa [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] using
        (RM.map f).card_subgroup_dvd_card
    have hc : Nat.Coprime (Nat.card (RM.map f)) 3 := by
      obtain ⟨n,hn⟩ := (hRp.map f).exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 2 3).pow_left n
    rcases (Nat.dvd_prime Nat.prime_two).mp (hc.dvd_mul_right.mp hd) with h | h
    · exact (hRne (card_eq_one.mp h)).elim
    · exact h
  let J := YM ⊔ RM
  have hJk : IsPGroup 2 (J ⊓ f.ker : Subgroup M) :=
    join_inf_ker_isPGroup_of_disjoint_images f YM RM le_normalizer_of_normal hkerp hRp
      ((IsPGroup.of_card (p := 3) (n := 1) (by simpa using hYc)).disjoint_of_ne
        3 2 (by decide) _ _ (hRp.map f))
  obtain ⟨_,⟨eJ⟩⟩ := product_twoCore_of_permThree f J
    (permThree_join_image_eq_top f YM RM hYc hRc) hJk
  have hJM : J = (Y ⊔ R).subgroupOf M := (subgroupOf_sup hYM hRM).symm
  let a : (Y ⊔ R : Subgroup G) ≃* J :=
    (subgroupOfEquivOfLe (sup_le hYM hRM)).symm.trans (MulEquiv.subgroupCongr hJM.symm)
  let b := a.toMonoidHom.pCoreQuotientEquiv (p := 2) a.surjective
    (IsPGroup.ker_isPGroup_of_injective a.injective)
  exact ⟨hmove,⟨b.trans eJ⟩⟩

theorem source_residual_actor_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (R : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hQR : (sourceResidual M Mc).pCoreIn 2 ≤ R) :
    let Y := sourceResidual M Mc
    (T : Subgroup G) ⊓ (Y ⊔ R) = R ∧ Chapter1.IsSylowIn 2 R (Y ⊔ R) := by
  let Y := sourceResidual M Mc
  let YM := Y.subgroupOf M
  let TM := T.subtype hM.1.2
  let C := (centralizer (localModule T M : Set G)).subgroupOf M
  let q := QuotientGroup.mk' C
  have hYM : Y ≤ M := sourceResidual_le _ _
  let : YM.Normal := residualY_normal M Mc
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    hM.1.2.trans ((normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal M Mc))
  obtain ⟨_,_,_,_,heY,hcore,_⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hYc : Nat.card (YM.map q) = 3 :=
    (Nat.card_congr heY.some.toEquiv).trans (Nat.card_zmod 3)
  have hdis : Disjoint (YM.map q) ((TM : Subgroup M).map q) :=
    (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hYc)).disjoint_of_ne
      3 2 (by decide) _ _ (TM.isPGroup'.map q)
  have hTYQ : (T : Subgroup G) ⊓ Y ≤ Y.pCoreIn 2 := by
    intro y hy
    rw [hcore]
    refine ⟨hy.2,?_⟩
    have hz : q ⟨y,hYM hy.2⟩ = 1 := hdis.le_bot
      ⟨mem_map_of_mem q hy.2,mem_map_of_mem q hy.1⟩
    exact (QuotientGroup.eq_one_iff (⟨y,hYM hy.2⟩ : M)).mp hz
  have hYR : R ≤ normalizer (Y : Set G) := hRT.trans hTY
  have hinter : (T : Subgroup G) ⊓ (Y ⊔ R) = R := by
    apply le_antisymm ?_ (le_inf hRT le_sup_right)
    intro x hx
    have hprod : x ∈ (Y : Set G)*(R : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left Y R hYR]
      exact hx.2
    obtain ⟨y,hy,r,hr,he⟩ := hprod
    have hyt : y ∈ (T : Subgroup G) := by
      have he' : y = x*r⁻¹ := by rw [←he]; group
      rw [he']
      exact T.mul_mem hx.1 (T.inv_mem (hRT hr))
    rw [←he]
    exact R.mul_mem (hQR (hTYQ ⟨hyt,hy⟩)) hr
  obtain ⟨P,hP⟩ := TM.exists_sylow_map_eq_inf_of_normal YM
  have hsM : Chapter1.IsSylowIn 2 ((TM : Subgroup M) ⊓ YM) YM := ⟨P,hP⟩
  have hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ Y) Y := by
    have hh := (Chapter1.IsSylowIn.map_iff M.subtype M.subtype_injective).mpr hsM
    simpa only [YM,TM,Subgroup.map_inf _ _ _ M.subtype_injective,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hM.1.2,map_subgroupOf_eq_of_le hYM] using hh
  obtain ⟨P',hP'⟩ := hs
  exact ⟨hinter,(T.isPGroup'.to_le hRT).exists_sylow_sup_of_coprime_index Y R hYR
    (P' : Subgroup Y) P'.not_dvd_index (hP'.trans_le (hTYQ.trans hQR))⟩

end CFSG.Quasithin.Chapter14.Section02
