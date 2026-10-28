module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SmallResidualNormalizer
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LocalAlternatingCore
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.SpecificGroups.Alternating.FourPairFixer

/-!
# The alternating residual crosses the opposite two-core

If the first local two-residual is A₄, its normal four-group cannot lie
in the opposite two-core. Otherwise their join has that opposite core as
a Sylow two-subgroup of index three. Primitivity excludes its normality,
and the local theorem (2.15) then makes its Sylow three-subgroups normal,
contradicting the contained A₄.

All local groups and inclusions belong to the actual cubic tree action;
the ambient group need not be finite. This is the first paragraph of
Goldschmidt (4.2), *Automorphisms of trivalent graphs* (1980), p.392.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem CubicTreeAction.local_twoCore_le_overlap (h : CubicTreeAction F) (i : Bool) :
    (F i).pCoreIn 2 ≤ F false ⊓ F true := by
  cases i
  · obtain ⟨P, hP⟩ := h.primitive.sylow.left_sylow
    have hm : (P : Subgroup (F false)).map (F false).subtype = F false ⊓ F true := by
      rw [hP, ← MonoidHom.range_comp]
      exact (F false ⊓ F true).range_subtype
    exact (map_mono (pCore_isPGroup.le_sylow_of_normal P)).trans_eq hm
  · obtain ⟨P, hP⟩ := h.primitive.sylow.right_sylow
    have hm : (P : Subgroup (F true)).map (F true).subtype = F false ⊓ F true := by
      rw [hP, ← MonoidHom.range_comp]
      exact (F false ⊓ F true).range_subtype
    exact (map_mono (pCore_isPGroup.le_sylow_of_normal P)).trans_eq hm

private theorem two_subgroup_le_alternating_core {A : Type*} [Group A]
    (e : A ≃* alternatingGroup (Fin 4)) (P : Subgroup A) (hp : IsPGroup 2 P) :
    P ≤ pCore 2 A := by
  have hp' := hp.map e.toMonoidHom
  obtain ⟨T, hT⟩ := hp'.exists_le_sylow
  rw [alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (by simp) T,
    ← AlternatingFourPair.twoCore_eq_kleinFour, ← pCore_map_iso 2 e] at hT
  exact (map_le_map_iff_of_injective e.injective).mp hT

private theorem alternating_no_normal_cubic {A : Type*} [Group A]
    (e : A ≃* alternatingGroup (Fin 4)) (P : Subgroup A) [P.Normal]
    (hc : Nat.card P = 3) : False := by
  let T := P.map e.toMonoidHom
  let : T.Normal := (inferInstance : P.Normal).map e.toMonoidHom e.surjective
  have hTc : Nat.card T = 3 := by rw [card_map_of_injective e.injective, hc]
  have ht := Theory.SpecificGroups.Alternating.FourPairFixer.normalizer_three_le_centralizer T hTc
  rw [T.normalizer_eq_top] at ht
  have hTZ : T ≤ center (alternatingGroup (Fin 4)) := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact (mem_centralizer_iff.mp (ht (mem_top y)) x hx).symm
  rw [alternatingGroup.center_eq_bot (by simp)] at hTZ
  have he := le_bot_iff.mp hTZ
  rw [he, card_bot] at hTc
  omega

/-- The residual four-group crosses the opposite two-core. -/
theorem CubicTreeAction.alternating_residual_core_not_le_opposite
    (h : CubicTreeAction F)
    (eR : pResidual 2 (F false) ≃* alternatingGroup (Fin 4)) :
    ¬ ((pResidual 2 (F false)).pCoreIn 2).map (F false).subtype ≤
      (F true).pCoreIn 2 := by
  intro hVR
  let : Finite (F false) := h.finite false
  let : Finite (F true) := h.finite true
  let S := (pResidual 2 (F false)).map (F false).subtype
  let V := S.pCoreIn 2
  let R := (F true).pCoreIn 2
  let H := S ⊔ R
  have hSA : S ≤ F false := map_subtype_le _
  have hRT : R ≤ F false ⊓ F true := h.local_twoCore_le_overlap true
  have hRA : R ≤ F false := hRT.trans inf_le_left
  have hHA : H ≤ F false := sup_le hSA hRA
  let : Finite H := Finite.of_injective (inclusion hHA) (inclusion_injective hHA)
  let : Finite S := Finite.of_injective (inclusion hSA) (inclusion_injective hSA)
  let : Finite R := Finite.of_injective (inclusion hRA) (inclusion_injective hRA)
  let eS : S ≃* alternatingGroup (Fin 4) :=
    (equivMapOfInjective (pResidual 2 (F false)) (F false).subtype
      (F false).subtype_injective).symm.trans eR
  have hVeq : V = ((pResidual 2 (F false)).pCoreIn 2).map (F false).subtype :=
    (map_pCoreIn_of_injective 2 _ _ (F false).subtype_injective).symm
  have hVR : V ≤ R := hVeq ▸ hVR
  have hVS : V ≤ S := pCoreIn_le 2 S
  have hS : Nat.card S = 12 := (Nat.card_congr eS.toEquiv).trans
    (alternatingGroup.card_of_card_eq_four (by simp))
  have hV : Nat.card V = 4 := by
    dsimp [V, pCoreIn]
    rw [card_map_of_injective S.subtype_injective,
      ← card_map_of_injective (K := pCore 2 S) (f := eS.toMonoidHom) eS.injective,
      pCore_map_iso, AlternatingFourPair.twoCore_eq_kleinFour,
      alternatingGroup.kleinFour_card_of_card_eq_four (by simp)]
  have hSR : S ⊓ R = V := by
    apply le_antisymm
    · have hp : IsPGroup 2 (R.subgroupOf S) := (isPGroup_pCoreIn 2 (F true)).comap_subtype
      have hh := map_mono (f := S.subtype) (two_subgroup_le_alternating_core eS _ hp)
      dsimp only [V, pCoreIn]
      simpa only [subgroupOf_map_subtype, inf_comm R S] using hh
    · exact le_inf hVS hVR
  have hSN : F false ≤ normalizer (S : Set G) := by
    have hh := (pResidual 2 (F false)).le_normalizer_map (F false).subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hRN : F true ≤ normalizer (R : Set G) :=
    (F true).le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 (F true)))
  let SH := S.subgroupOf H
  let RH := R.subgroupOf H
  have hSH : S ≤ H := le_sup_left
  have hRH : R ≤ H := le_sup_right
  let : SH.Normal := (normal_subgroupOf_iff_le_normalizer hSH).mpr (hHA.trans hSN)
  have hSRH : SH ⊔ RH = ⊤ := by rw [← subgroupOf_sup hSH hRH, subgroupOf_self]
  have hSc : Nat.card SH = 12 := (Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv).trans hS
  have hRc : Nat.card RH = Nat.card R := Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv
  have hIc : Nat.card (SH ⊓ RH : Subgroup H) = 4 := by
    change Nat.card ((S ⊓ R).subgroupOf H) = 4
    rw [hSR]
    exact (Nat.card_congr (subgroupOfEquivOfLe (hVS.trans hSH)).toEquiv).trans hV
  have hH : Nat.card H = 3 * Nat.card R := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes SH RH
      (by rw [normalizer_eq_top]; exact le_top)
    rw [hSc, hRc, hIc, hSRH, card_top] at hh
    omega
  have hi : RH.index = 3 := by
    have hh := RH.index_mul_card
    rw [hRc, hH] at hh
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hh
  have hp : IsPGroup 2 RH := (isPGroup_pCoreIn 2 (F true)).comap_subtype
  let P : Sylow 2 H := hp.toSylow (by rw [hi]; decide)
  have hP : (P : Subgroup H).map H.subtype = R := map_subgroupOf_eq_of_le hRH
  have hX3 : 3 ∣ Nat.card S := hS ▸ (by decide)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S) 3 hX3
  let XH := (zpowers x).map (inclusion hSH)
  have hXH : Nat.card XH = 3 := by
    rw [card_map_of_injective (inclusion_injective hSH), Nat.card_zpowers, hx]
  have hn : ¬ (P : Subgroup H).Normal := by
    intro hpn
    let : (P : Subgroup H).Normal := hpn
    have hHN : H ≤ normalizer (R : Set G) := by
      have hh := (P : Subgroup H).le_normalizer_map H.subtype
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, hP] using hh
    let X := (zpowers x).map (inclusion hSA)
    have hX : Nat.card X = 3 := by
      rw [card_map_of_injective (inclusion_injective hSA), Nat.card_zpowers, hx]
    obtain ⟨PB, hPB⟩ := h.primitive.sylow.right_sylow
    have hdB : 3 ∣ Nat.card (F true) := by
      have hii : (PB : Subgroup (F true)).index = 3 := by rw [hPB]; exact h.primitive.right_index
      rw [← (PB : Subgroup (F true)).index_mul_card, hii]
      exact dvd_mul_right _ _
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := F true) 3 hdB
    have he := h.normalized_overlap_eq_bot_of_three_subgroups R hRT X (zpowers y)
      hX (by rw [Nat.card_zpowers, hy])
      (by rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩; exact hHN (hSH z.property))
      ((map_subtype_le _).trans hRN)
    have hvbot : V = ⊥ := bot_unique (hVR.trans_eq he)
    rw [hvbot, card_bot] at hV
    omega
  have hstrict : pCore 2 H < (P : Subgroup H) :=
    lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal P) (fun he => hn (by rw [← he]; infer_instance))
  obtain ⟨eH⟩ := sylow_index_three_core_quotient P hi hstrict
  have hall := h.normal_three_of_opposite_normalized_sylow H hHA P
    (hP ▸ hRT) (hP ▸ hRN) eH
  have hp3 : IsPGroup 3 XH := IsPGroup.of_card (n := 1) (by simpa using hXH)
  have hiX : ¬ 3 ∣ XH.index := by
    have hh := XH.index_mul_card
    rw [hXH, hH] at hh
    have he : XH.index = Nat.card R := by omega
    rw [he]
    obtain ⟨n, hn⟩ := (isPGroup_pCoreIn 2 (F true)).exists_card_eq
    rw [hn]
    intro hd
    have hd2 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hd
    norm_num at hd2
  let TX := hp3.toSylow hiX
  let : XH.Normal := hall TX
  let XS := XH.comap (inclusion hSH)
  have hXS : XS = zpowers x := comap_map_eq_self_of_injective (inclusion_injective hSH) _
  let : (zpowers x).Normal := hXS ▸ inferInstanceAs XS.Normal
  exact alternating_no_normal_cubic eS (zpowers x) (by rw [Nat.card_zpowers, hx])

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
