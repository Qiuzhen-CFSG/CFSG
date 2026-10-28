module
public import CFSG.Quasithin.ChapterC.Section06.CubicRecognition
public import Theory.GroupTheory.ElementarySwappedPair
public import Theory.GroupTheory.TwoElementaryIndexTwo
public import Theory.GroupTheory.SymmetricFourModelCoreData
public import Theory.GroupAction.MaximalCosetOrbit
public import Stellmacher.ElementaryAbelianMaxPair.Normalizers

/-!
# Thompson stability for the original large single A₃ branch

The recognized C₂ × S₄ group has a Sylow group of order 16 and two elementary subgroups of order eight. Every element outside the source Sylow swaps this pair. An elementary subgroup of order at least eight outside it would centralize their intersection, hence normalize the nontrivial central factor. The original common-normal obstruction excludes that possibility and gives J(M₀)=J(R).

Source: Aschbacher–Smith C.6.1, printed p.165.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {H M K R : Subgroup G}

theorem cubic_large_core_thompson_from_original
    (c : OriginalHypotheses H M K R R) {F : Type*} [Field F]
    (h : RankOne.Setup R K F) (hK : IsAlternatingBlock K 3)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G))
    (hlarge : H.pCoreIn 2 ≠ sourceModule K) :
    elementaryAbelianMaxJ M = elementaryAbelianMaxJ R := by
  let Q := H.pCoreIn 2
  let W := Q.map (MulAut.conj x⁻¹).toMonoidHom
  let D := R ⊓ centralizer (K : Set G)
  have hf := rankOne_family_from_original c h hi x hx hnc
  have hb := cubic_baumann_eq_original c h hK hi x hx hnc
  have hJ : elementaryAbelianMaxJ R = R := hf.2.1.symm.trans hb
  have hfamily : elementaryAbelianMaxSubgroups R = {Q,W} := hf.2.2.1
  have hQmax : Q ∈ elementaryAbelianMaxSubgroups R := hfamily ▸ Set.mem_insert _ _
  have hWmax : W ∈ elementaryAbelianMaxSubgroups R := hfamily ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)
  let := hQmax.2.1
  let := hWmax.2.1
  have hQN : R ≤ normalizer (Q : Set G) := c.R_le_H.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hne : Q ≠ W := by
    intro he
    apply hnc
    have hUQ := h.module_le_core
    rw [hf.1] at hUQ
    exact ((map_mono hUQ).trans_eq he.symm).trans ((hf.1 ▸ h.core).le.trans inf_le_right)
  have hjoin : Q ⊔ W = R := by
    have hh := h.core_span (c.R_normal hx) hnc
    simpa only [hf.1,RankOne.S,hb] using hh.symm
  obtain ⟨hDcard,⟨e⟩⟩ := cubic_large_core_model_from_original c h hK hi x hx hnc hlarge
  have hHcard : Nat.card H = 48 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod,Nat.card_perm,Nat.card_fin]
    norm_num
  have hmodel := symmetric_four_model_twoCore_data (Or.inr ⟨e⟩)
  have hQcard : Nat.card Q = 8 := by
    have hc : Nat.card (pCore 2 H) = 8 := by rcases hmodel.2 with hh | hh <;> omega
    exact (card_map_of_injective H.subtype_injective).trans hc
  have hWcard : Nat.card W = 8 := (card_map_of_injective (MulAut.conj x⁻¹).injective).trans hQcard
  have hRcard : Nat.card R = 16 := by
    rw [←c.sylow_image,card_map_of_injective H.subtype_injective,c.sylow.card_eq_multiplicity,hHcard]
    rw [show (48:ℕ)=2^4*3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,Nat.prime_three.factorization]
  have hIcard : Nat.card (Q ⊓ W : Subgroup G) = 4 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q W (hWmax.1.trans hQN)
    rw [hQcard,hWcard,hjoin,hRcard] at hh
    omega
  have hQi : (Q.subgroupOf R).index = 2 := by
    have hh := (Q.subgroupOf R).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hQmax.1).toEquiv,hQcard,hRcard] at hh
    omega
  have hWi : (W.subgroupOf R).index = 2 := by
    have hh := (W.subgroupOf R).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hWmax.1).toEquiv,hWcard,hRcard] at hh
    omega
  have hpair (A : Subgroup G) (hAR : A ≤ R) (hA : IsElementaryAbelian 2 A) : A ≤ Q ∨ A ≤ W := by
    let := hA
    have hQR : IsElementaryAbelian 2 (Q.subgroupOf R) := IsElementaryAbelian.subgroupOf hQmax.1
    have hWR : IsElementaryAbelian 2 (W.subgroupOf R) := IsElementaryAbelian.subgroupOf hWmax.1
    have hn : Q.subgroupOf R ≠ W.subgroupOf R := by
      intro he
      apply hne
      have hm := congrArg (map R.subtype) he
      simpa only [map_subgroupOf_eq_of_le hQmax.1,map_subgroupOf_eq_of_le hWmax.1] using hm
    have hRne : ¬ IsElementaryAbelian 2 R := by
      intro he
      let := he
      apply hnc
      intro v hv u hu
      exact setLike_mul_comm ((h.module_le.trans inf_le_left) hu)
        (((h.conjugate_le (c.R_normal hx)).trans inf_le_left) hv)
    rcases elementary_le_one_of_two_index_two (Q.subgroupOf R) (W.subgroupOf R)
        hQR hWR hQi hWi hn hRne (A.subgroupOf R) (IsElementaryAbelian.subgroupOf hAR) with ha | ha
    · exact Or.inl (fun a haA => ha (show (⟨a,hAR haA⟩:R) ∈ A.subgroupOf R from haA))
    · exact Or.inr (fun a haA => ha (show (⟨a,hAR haA⟩:R) ∈ A.subgroupOf R from haA))
  have hQM : ¬ M ≤ normalizer (Q : Set G) := by
    intro hh
    exact hne (mem_normalizer_iff_map_conj_eq.mp (hh (M.inv_mem hx))).symm
  have hout (A : Subgroup G) (hRA : R ≤ normalizer (A : Set G))
      (hMA : ¬ M ≤ normalizer (A : Set G)) (y : G) (hy : y ∈ M) (hyr : y ∉ R) :
      y ∉ normalizer (A : Set G) := by
    intro hya
    apply hMA
    rw [←sup_zpowers_eq_of_relIndex_prime c.R_le_M Nat.prime_two hi hy hyr]
    exact sup_le hRA (zpowers_le.mpr hya)
  have hswap (y : G) (hy : y ∈ M) (hyr : y ∉ R) :
      Q.map (MulAut.conj y).toMonoidHom = W ∧ W.map (MulAut.conj y).toMonoidHom = Q := by
    have hp (A : Subgroup G) (ha : A ∈ elementaryAbelianMaxSubgroups R) :
        A.map (MulAut.conj y).toMonoidHom = Q ∨ A.map (MulAut.conj y).toMonoidHom = W := by
      simpa only [Subgroup.conjBy,hfamily,Set.mem_insert_iff,Set.mem_singleton_iff] using
        maxFamily_conj_mem ha (c.R_normal hy)
    have hq := (hp Q hQmax).resolve_left (fun he => hout Q hQN hQM y hy hyr (mem_normalizer_iff_map_conj_eq.mpr he))
    refine ⟨hq,?_⟩
    rcases hp W hWmax with hw | hw
    · exact hw
    · exact (hne (map_injective (MulAut.conj y).injective (hq.trans hw.symm))).elim
  have hp := cubic_product_from_original c h hK hi x hx hnc
  have hd := cubic_centralizer_rank_from_original c h hK hi x hx hnc
  let : IsElementaryAbelian 2 D := hd.1
  have hDH : D ≤ centralizer (H : Set G) := by
    rw [←hp.1]
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer D) (le_centralizer_iff.mp hp.2.2.1)
  have hDN : R ≤ normalizer (D : Set G) :=
    c.R_le_H.trans ((le_centralizer_iff.mp hDH).trans (Subgroup.centralizer_le_normalizer _))
  have hDM : ¬ M ≤ normalizer (D : Set G) := by
    intro hm
    have hz : D = ⊥ := c.no_common_normal D inf_le_left
      ((normal_subgroupOf_iff_le_normalizer
        (inf_le_left.trans (c.R_le_M.trans le_sup_left))).mpr
        (sup_le hm ((le_centralizer_iff.mp hDH).trans (Subgroup.centralizer_le_normalizer _))))
    have hc : Nat.card D = 2 := hDcard
    rw [hz,card_bot] at hc
    omega
  have hDI : D ≤ Q ⊓ W := by
    have he : D = RankOne.D R K := by change R ⊓ _ = ChapterB.baumann R ⊓ _; rw [hb]
    apply le_inf
    · change D ≤ H.pCoreIn 2
      rw [←hf.1,(h.factorization (c.R_normal hx) hnc).core,←he]
      exact le_sup_right
    · change D ≤ (H.pCoreIn 2).map _
      rw [←hf.1,←h.opposite_eq_conjugate (c.R_normal hx) hnc,←he]
      exact le_sup_right
  have hCI : M ⊓ centralizer ((Q ⊓ W : Subgroup G) : Set G) ≤ R := by
    rintro y ⟨hy,hyc⟩
    by_contra hyr
    exact hout D hDN hDM y hy hyr (Subgroup.centralizer_le_normalizer _ (centralizer_le hDI hyc))
  have hex (A : Subgroup G) (haM : A ≤ M) (ha : IsElementaryAbelian 2 A) (hc : 8 ≤ Nat.card A) : A ≤ R :=
    elementary_le_of_swapped_pair R M Q W c.R_le_M c.R_normal hi hQmax.1 hWmax.1 hIcard hpair hswap hCI A haM ha hc
  have hbound (A : Subgroup G) (haM : A ≤ M) (ha : IsElementaryAbelian 2 A) : Nat.card A ≤ 8 := by
    by_cases hc : 8 ≤ Nat.card A
    · exact (hQmax.2.2 A (hex A haM ha hc) ha).trans_eq hQcard
    · omega
  have hQMmax : Q ∈ elementaryAbelianMaxSubgroups M :=
    ⟨hQmax.1.trans c.R_le_M,hQmax.2.1,fun A haM ha => (hbound A haM ha).trans_eq hQcard.symm⟩
  have hWMmax : W ∈ elementaryAbelianMaxSubgroups M :=
    ⟨hWmax.1.trans c.R_le_M,hWmax.2.1,fun A haM ha => (hbound A haM ha).trans_eq hWcard.symm⟩
  rw [hJ]
  apply le_antisymm
  · apply sSup_le
    intro A ha
    exact hex A ha.1 ha.2.1 (hQcard ▸ ha.2.2 Q hQMmax.1 hQMmax.2.1)
  · rw [←hjoin]
    exact sup_le (le_sSup hQMmax) (le_sSup hWMmax)
end CFSG.Quasithin.ChapterC.Section06
