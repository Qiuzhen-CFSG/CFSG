module
public import Theory.GroupTheory.FourFamilyAction.Endgame
public import Theory.GroupAction.IndexedSubgroupFamily
public import Theory.GroupTheory.PGroup.InvariantThompsonPairNormalizer

/-!
# A large mixed normalizer from the four-point action

A finite two-group normalizing the Thompson subgroup permutes its four
maximum elementary subgroups. If the core stabilizer is S and an index-two
overgroup M preserves the invariant opposite pair, the image of M is the
nonregular Klein four. A larger image is dihedral of order eight; its edge
stabilizer has the same order as the point stabilizer S. This gives a mixed
subgroup normalizer of at least that order without a faithful-action premise.

Source application: Aschbacher–Smith, double linear case of 2.4.7,
printed pp.540–541.
-/

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory.FourFamilyAction
variable {G : Type*} [Group G] [Finite G]

/-- The four-point normalizer alternative does not require the pointwise
kernel to equal the Thompson subgroup. It uses the actual core stabilizer. -/
theorem normalizer_eq_or_large_mixed
    (P M S : Subgroup G) (hP : IsPGroup 2 P) (hSM : S ≤ M) (hMP : M ≤ P)
    (hi : S.relIndex M = 2)
    (f : Fin 4 → Subgroup G) (hinj : Function.Injective f)
    (hfamily : Set.range f = elementaryAbelianMaxSubgroups S)
    (hpair : {A ∈ elementaryAbelianMaxSubgroups S | S ≤ normalizer (A : Set G)} =
      {f 0,f 1})
    (hcontrol : P ⊓ normalizer (f 0 : Set G) = S) :
    P ⊓ normalizer (elementaryAbelianMaxJ S : Set G) = M ∨
      Nat.card S ≤ Nat.card (P ⊓ normalizer ((f 0 ⊔ f 2 : Subgroup G) : Set G) : Subgroup G) := by
  classical
  let N := P ⊓ normalizer (elementaryAbelianMaxJ S : Set G)
  have hMS : M ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM).mp (normal_of_index_eq_two hi)
  have hMN : M ≤ N := le_inf hMP
    (hMS.trans (normalizer_le_normalizer_elementaryAbelianMaxJ S))
  have hSN : S ≤ N := hSM.trans hMN
  have hinv (g : N) (i : Fin 4) : ∃ j, f j = (f i).conjBy (g : G) := by
    have hfi : f i ∈ elementaryAbelianMaxSubgroups S := hfamily ▸ ⟨i,rfl⟩
    rw [←maxFamily_thompson] at hfi
    have hm := (maxFamily_map_injective_iff (MulAut.conj (g : G)).toMonoidHom
      (MulAut.conj (g : G)).injective (elementaryAbelianMaxJ S) (f i)).mpr hfi
    have he : (elementaryAbelianMaxJ S).map (MulAut.conj (g : G)).toMonoidHom =
        elementaryAbelianMaxJ S := mem_normalizer_iff_map_conj_eq.mp g.property.2
    rw [he,maxFamily_thompson,←hfamily] at hm
    exact hm
  let ρ := IndexedSubgroupFamily.action N f hinj hinv
  have hfix (g : N) (i : Fin 4) : ρ g i = i ↔ (g : G) ∈ normalizer (f i : Set G) :=
    IndexedSubgroupFamily.action_fixed_iff N f hinj hinv g i
  have hzero (g : N) : ρ g 0 = 0 ↔ (g : G) ∈ S := by
    rw [hfix]
    exact ⟨fun hn => hcontrol ▸ ⟨g.property.1,hn⟩,
      fun hs => (hcontrol.symm ▸ hs).2⟩
  have hfixS (i : Fin 4) (hi : i=0 ∨ i=1) : S ≤ normalizer (f i : Set G) := by
    have hm : f i ∈ {A ∈ elementaryAbelianMaxSubgroups S | S ≤ normalizer (A : Set G)} := by
      rw [hpair]
      rcases hi with rfl | rfl <;> simp
    exact hm.2
  have hle : (M.subgroupOf N).map ρ ≤ pairGroup := by
    rintro p ⟨g,hg,rfl⟩
    apply (mem_pair_iff (ρ g)).mpr
    have ha (i j : Fin 4)
        (hp : {A ∈ elementaryAbelianMaxSubgroups S | S ≤ normalizer (A : Set G)} =
          {f i,f j}) : ρ g i = i ∨ ρ g i = j := by
      have hh := normalizer_preserves_invariant_maxFamily_pair S (f i) (f j) hp (hMS hg)
      have he := IndexedSubgroupFamily.action_apply N f hinj hinv g i
      exact hh.imp (fun hi => hinj (he.trans hi)) (fun hj => hinj (he.trans hj))
    exact ⟨ha 0 1 hpair,(ha 1 0 (hpair.trans (Set.pair_comm _ _))).symm⟩
  have hmoveS : ∃ s ∈ S, s ∉ normalizer (f 2 : Set G) := by
    by_contra! hh
    have hm : f 2 ∈ {A ∈ elementaryAbelianMaxSubgroups S | S ≤ normalizer (A : Set G)} :=
      ⟨hfamily ▸ ⟨2,rfl⟩,hh⟩
    rw [hpair] at hm
    rcases Set.mem_insert_iff.mp hm with he | he
    · exact (by decide : (2:Fin 4) ≠ 0) (hinj he)
    · exact (by decide : (2:Fin 4) ≠ 1) (hinj (Set.mem_singleton_iff.mp he))
  obtain ⟨s,hs,hsn⟩ := hmoveS
  let sN : N := ⟨s,hSN hs⟩
  have hsr : ρ sN = rightSwap := by
    have h0 := (hzero sN).mpr hs
    have h1 := (hfix sN 1).mpr (hfixS 1 (Or.inr rfl) hs)
    have h2 : ρ sN 2 ≠ 2 := fun he => hsn ((hfix sN 2).mp he)
    exact (by decide +kernel : ∀ p : Perm, p 0 = 0 → p 1 = 1 → p 2 ≠ 2 → p=rightSwap)
      (ρ sN) h0 h1 h2
  have hright : rightSwap ∈ (M.subgroupOf N).map ρ := ⟨sN,hSM hs,hsr⟩
  have hlt : S < M := lt_of_le_of_ne hSM (by
    intro he
    have hh : S.relIndex M=1 := relIndex_eq_one.mpr he.ge
    omega)
  obtain ⟨x,hx,hxs⟩ := SetLike.exists_of_lt hlt
  let xN : N := ⟨x,hMN hx⟩
  have hximage : ρ xN ∈ (M.subgroupOf N).map ρ := ⟨xN,hx,rfl⟩
  have hxzero : ρ xN 0 ≠ 0 := fun he => hxs ((hzero xN).mp he)
  have hleft : leftSwap ∈ (M.subgroupOf N).map ρ := by
    have hh := (by decide +kernel : ∀ p : Perm, (∃ i,word i=p) → p 0 ≠ 0 →
      p=leftSwap ∨ p*rightSwap=leftSwap) (ρ xN) (hle hximage) hxzero
    rcases hh with hh | hh
    · exact hh ▸ hximage
    · exact hh ▸ ((M.subgroupOf N).map ρ).mul_mem hximage hright
  have himage : (M.subgroupOf N).map ρ = pairGroup := by
    apply le_antisymm hle
    rintro p ⟨i,rfl⟩
    fin_cases i
    · exact ((M.subgroupOf N).map ρ).one_mem
    · exact hleft
    · exact hright
    · exact ((M.subgroupOf N).map ρ).mul_mem hleft hright
  have hkS : ρ.ker ≤ S.subgroupOf N := by
    intro g hg
    apply (hzero g).mp
    change ρ g = 1 at hg
    rw [hg]
    rfl
  have hpre : pairGroup.comap ρ = M.subgroupOf N := by
    rw [←himage,comap_map_eq,sup_of_le_left (hkS.trans (subgroupOf_mono N hSM))]
  have hNtwo : IsPGroup 2 N := hP.to_le inf_le_left
  have hρtwo : IsPGroup 2 ρ.range := hNtwo.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hl := (map_le_range ρ (M.subgroupOf N)) hleft
  have hr := (map_le_range ρ (M.subgroupOf N)) hright
  rcases pair_or_full ρ.range hρtwo hl hr with he | he
  · left
    apply le_antisymm _ hMN
    intro g hg
    exact hpre.le (he ▸ (show ρ (⟨g,hg⟩ : N) ∈ ρ.range from ⟨⟨g,hg⟩,rfl⟩))
  · right
    have himS : (S.subgroupOf N).map ρ = zpowers rightSwap := by
      apply le_antisymm
      · rintro p ⟨g,hg,rfl⟩
        have h0 := (hzero g).mpr hg
        have hm : ρ g ∈ fullGroup := he ▸ (show ρ g ∈ ρ.range from ⟨g,rfl⟩)
        have hh := (by decide +kernel : ∀ p : Perm, (∃ i,doubleWord i=p) → p 0=0 →
          p=1 ∨ p=rightSwap) (ρ g) hm h0
        rcases hh with hh | hh
        · exact hh ▸ one_mem _
        · exact hh ▸ mem_zpowers rightSwap
      · apply zpowers_le.mpr
        exact ⟨sN,hs,hsr⟩
    let A := (zpowers crossSwap).comap ρ
    have hAr : zpowers crossSwap ≤ ρ.range := by
      apply zpowers_le.mpr
      rw [he]
      exact ⟨4,rfl⟩
    have hAmap : A.map ρ = zpowers crossSwap := by
      rw [map_comap_eq,inf_of_le_right hAr]
    have hkA : ρ.ker ≤ A := by
      intro g hg
      change ρ g ∈ zpowers crossSwap
      change ρ g=1 at hg
      rw [hg]
      exact one_mem _
    have hcS := relIndex_mul_relIndex (⊥ : Subgroup N) ρ.ker (S.subgroupOf N) bot_le hkS
    have hcA := relIndex_mul_relIndex (⊥ : Subgroup N) ρ.ker A bot_le hkA
    rw [relIndex_bot_left,relIndex_bot_left] at hcS hcA
    rw [relIndex_ker,himS,Nat.card_zpowers] at hcS
    rw [relIndex_ker,hAmap,Nat.card_zpowers] at hcA
    have hor : orderOf rightSwap=2 := orderOf_eq_prime
      (by decide +kernel) (by decide +kernel)
    have hoc : orderOf crossSwap=2 := orderOf_eq_prime
      (by decide +kernel) (by decide +kernel)
    have ho : orderOf rightSwap=orderOf crossSwap := hor.trans hoc.symm
    have hc : Nat.card S = Nat.card A := by
      rw [ho] at hcS
      rw [Nat.card_congr (subgroupOfEquivOfLe hSN).toEquiv] at hcS
      omega
    rw [hc]
    have hcmap : Nat.card (A.map N.subtype) = Nat.card A := card_map_of_injective N.subtype_injective
    rw [←hcmap]
    apply card_le_of_le
    rintro a ⟨g,hg,rfl⟩
    refine ⟨g.property.1,mem_normalizer_iff_map_conj_eq.mpr ?_⟩
    have hgρ : ρ g=1 ∨ ρ g=crossSwap := by
      obtain ⟨k,hk,hpow⟩ := Finset.mem_image.mp
        (mem_zpowers_iff_mem_range_orderOf.mp (show ρ g ∈ zpowers crossSwap from hg))
      have hcross : orderOf crossSwap = 2 := hoc
      have hk' : k=0 ∨ k=1 := by
        have hh := Finset.mem_range.mp hk
        rw [hcross] at hh
        omega
      rcases hk' with rfl | rfl
      · exact Or.inl (by simpa only [pow_zero] using hpow.symm)
      · exact Or.inr (by simpa only [pow_one] using hpow.symm)
    change (f 0 ⊔ f 2).map (MulAut.conj (g:G)).toMonoidHom = _
    rw [Subgroup.map_sup]
    change (f 0).conjBy (g:G) ⊔ (f 2).conjBy (g:G) = f 0 ⊔ f 2
    rw [←IndexedSubgroupFamily.action_apply N f hinj hinv g 0,
      ←IndexedSubgroupFamily.action_apply N f hinj hinv g 2]
    rcases hgρ with hh | hh
    · rw [hh]
      rfl
    · rw [hh]
      exact sup_comm _ _

end Theory.GroupTheory.FourFamilyAction
