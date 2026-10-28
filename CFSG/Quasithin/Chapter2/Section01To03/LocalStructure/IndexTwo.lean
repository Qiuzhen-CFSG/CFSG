module

public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Thompson

/-!
# The index-two β criterion

Source: Aschbacher–Smith 2.3.8(5b) and 2.3.9(8), printed pp.524–526.
If the normalizer condition for R fails, choose a largest bad two-overgroup V.
Its normalizer W in a Sylow subgroup of M is strictly larger; maximality of V
makes W a β-subgroup. Since V has characteristic-two normalizer, W is a local
base. But R < V < W forces |W| > 2|R| = |S|, contradicting 2.3.6.
Thompson heredity and 2.3.8(5a) supply the initial normalizer control for R.
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G] {M H U L : Subgroup G}

omit [Finite G] in
private theorem card_mul_relIndex {A B : Subgroup G} (h : A ≤ B) :
    Nat.card A * A.relIndex B = Nat.card B := by
  have hc := (A.subgroupOf B).card_mul_index
  rwa [Nat.card_congr (subgroupOfEquivOfLe h).toEquiv] at hc

private theorem double_card_le_of_lt {A B : Subgroup G} (h : A < B) :
    2 * Nat.card A ≤ Nat.card B := by
  have hne : A.relIndex B ≠ 1 := fun he => h.not_ge (relIndex_eq_one.mp he)
  have hn : A.relIndex B ≠ 0 := by
    intro he
    have hc := card_mul_relIndex h.le
    rw [he, mul_zero] at hc
    exact (Nat.card_pos (α := B)).ne hc
  have hi : 2 ≤ A.relIndex B := by omega
  calc
    2 * Nat.card A ≤ A.relIndex B * Nat.card A := Nat.mul_le_mul_right _ hi
    _ = Nat.card B := by rw [Nat.mul_comm, card_mul_relIndex h.le]

private theorem thompson_eq_of_intermediate (A R : Subgroup G)
    (hJR : elementaryAbelianMaxJ A ≤ R) (hRA : R ≤ A) :
    elementaryAbelianMaxJ A = elementaryAbelianMaxJ R := by
  have h₁ := elementaryAbelianMaxOrder_le_and_j_le_of_eq R A hRA
  have h₂ := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le A R hJR
  have he := le_antisymm h₁.1 h₂.1
  exact le_antisymm (h₂.2 he.symm) (h₁.2 he)

/-- The maximal bad-overgroup argument, separating the local input from
the Thompson subgroup application. -/
theorem beta_of_index_two_local_bound (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    {R : Subgroup G} (hR : R ∈ Chapter1.S2e G) (hRM : R ≤ M)
    (hNR : normalizer (R : Set G) ≤ M)
    (hc : twoCore M ⊓ centralizer (R : Set G) ≤ R)
    (hcard : twoPart H = 2 * Nat.card R) : R ∈ beta M := by
  refine ⟨⟨hR.1, hR.2.1⟩, hRM, ?_, hc⟩
  intro V hV hRV hVM
  by_contra hbad
  let bad : Subgroup G → Prop := fun V =>
    IsPGroup 2 V ∧ R ≤ V ∧ V ≤ M ∧ ¬ normalizer (V : Set G) ≤ M
  obtain ⟨V, hVV, hmax⟩ := Finite.exists_le_maximal (show bad V from ⟨hV.2, hRV, hVM, hbad⟩)
  have hVp := hmax.1.1
  have hRV : R ≤ V := hmax.1.2.1
  have hVM : V ≤ M := hmax.1.2.2.1
  have hbad : ¬ normalizer (V : Set G) ≤ M := hmax.1.2.2.2
  have hRVlt : R < V := lt_of_le_of_ne hRV (fun he => hbad (he ▸ hNR))
  obtain ⟨P, hVP⟩ := (hVp.comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
  let B := (P : Subgroup M).map M.subtype
  have hVB : V ≤ B := by
    have hm := map_mono hVP (f := M.subtype)
    change (V.subgroupOf M).map M.subtype ≤ _ at hm
    rwa [map_subgroupOf_eq_of_le hVM] at hm
  let W := B ⊓ normalizer (V : Set G)
  have hVW : V ≤ W := le_inf hVB V.le_normalizer
  have hBWp := P.isPGroup'.map M.subtype
  have hWp : IsPGroup 2 W := hBWp.to_le inf_le_left
  have hWne : W ≠ ⊥ := fun he => hR.1 (bot_unique (he ▸ hRV.trans hVW))
  have hcore : twoCore (normalizer (V : Set G)) ≠ ⊥ := by
    intro he
    apply hR.1
    exact bot_unique (he ▸ hRV.trans (le_pCoreIn_of_normalizes hVp V.le_normalizer le_rfl))
  have hVWlt : V < W := by
    refine lt_of_le_of_ne hVW ?_
    intro he
    let : Group.IsNilpotent B := hBWp.isNilpotent
    have hself : normalizer (V.subgroupOf B : Set B) = V.subgroupOf B := by
      apply le_antisymm _ le_normalizer
      rw [← subgroupOf_normalizer_eq hVB]
      intro x hx
      exact (show (x : G) ∈ V from he ▸ ⟨x.property, hx⟩)
    have htop := normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := B)) _ hself
    apply hbad
    exact core_overgroup_le_of_sylow T hTM hunique hcore P
      ((subgroupOf_eq_top.mp htop).trans V.le_normalizer)
  have hWb : W ∈ beta M := by
    refine ⟨⟨hWne, hWp⟩, inf_le_left.trans (map_subtype_le _), ?_, ?_⟩
    · intro X hX hWX hXM
      by_contra hXN
      have hVX : V ≤ X := hVW.trans hWX
      have he := hmax.2 ⟨hX.2, hRV.trans hVX, hXM, hXN⟩ hVX
      exact hVWlt.not_ge (hWX.trans he)
    · exact (inf_le_inf_left _ (centralizer_le (hRV.trans hVW))).trans (hc.trans (hRV.trans hVW))
  have hVe := Chapter1.lemma_1_1_4_1 hR hRV hVp
  have hbase : W ∈ localBases (Chapter1.He G) M :=
    ⟨normalizer (V : Set G), hWb, hVe.2.2, hcore, inf_le_right, hbad⟩
  have hb := gammaZero_card_bound hH hbase
  have h₁ := double_card_le_of_lt hRVlt
  have h₂ := double_card_le_of_lt hVWlt
  have hpos := Nat.card_pos (α := R)
  omega

/-- Lemma 2.3.8(5b), with the literal relative index in S. -/
theorem lemma_2_3_8_5b {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    {R : Subgroup G} (hJR : elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) ≤ R)
    (hRS : R ≤ (S : Subgroup H).map H.subtype)
    (hi : R.relIndex ((S : Subgroup H).map H.subtype) = 2)
    (hc : twoCore M ⊓ centralizer (R : Set G) ≤ R) : R ∈ beta M := by
  have hJ := gammaZero_thompson_mem_S2e hG T hM hTM hunique hH hpair S hUS
  have hJeq := thompson_eq_of_intermediate _ R hJR hRS
  have hNR : normalizer (R : Set G) ≤ M := by
    apply le_trans _ (lemma_2_3_8_5a hG T hM hTM hunique hH hpair S hUS)
    rw [hJeq]
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq] at hx ⊢
    change R.map (MulAut.conj x).toMonoidHom = R at hx
    change (elementaryAbelianMaxJ R).map (MulAut.conj x).toMonoidHom = _
    rw [← elementaryAbelianMaxJ_map_equiv (MulAut.conj x) R, hx]
  have hSb := beta_mono hpair.1.1 hUS (S.isPGroup'.map H.subtype)
  apply beta_of_index_two_local_bound T hTM hunique hH
    (Chapter1.lemma_1_1_4_1 hJ hJR ((S.isPGroup'.map H.subtype).to_le hRS))
    (hRS.trans hSb.2.1) hNR hc
  have he := card_mul_relIndex hRS
  rw [hi, sylow_image_card] at he
  omega

/-- Lemma 2.3.9(8): its centralizer premise is discharged by part (2). -/
theorem lemma_2_3_9_8 {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    {R : Subgroup G} (hJR : elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) ≤ R)
    (hQR : twoCore H ≤ R) (hRS : R ≤ (S : Subgroup H).map H.subtype)
    (hi : R.relIndex ((S : Subgroup H).map H.subtype) = 2)
    (hCR : (S : Subgroup H).map H.subtype ⊓ centralizer (R : Set G) ≤ R) : R ∈ beta M :=
  lemma_2_3_8_5b hG T hM hTM hunique hH hpair S hUS hJR hRS hi
    (centralizer_core_le_of_le (twoCore H) R _ (lemma_2_3_9_2 hH hpair S hUS) hQR hCR)

end CFSG.Quasithin.Chapter2
