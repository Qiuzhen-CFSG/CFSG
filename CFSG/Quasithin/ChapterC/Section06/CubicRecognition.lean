module
public import CFSG.Quasithin.ChapterC.Section06.RankOneSource
public import CFSG.Quasithin.ChapterC.Section06.CentralizerRank
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree
public import Theory.GroupTheory.FourGroupTwoGroupAction
public import Theory.GroupTheory.AlternatingFourExtensionRecognition
public import Theory.GroupTheory.MarkedInternalProduct

/-!
# The original single A₃ recognition in C.6.1

The nontrivial conjugate four-group supplies the full two-group action on U. Thus the original Sylow subgroup equals its Baumann subgroup. Its product with K is the actual S₄ factor; the full centralizer C_R(K) splits off. The original core distinguishes S₄ from C₂ × S₄.

Source: Aschbacher–Smith C.6.1, printed p.165. All groups and conjugation maps remain the original source groups.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {H M K R : Subgroup G}

theorem cubic_baumann_eq_original
    (c : OriginalHypotheses H M K R R) {F : Type*} [Field F]
    (h : RankOne.Setup R K F) (hK : IsAlternatingBlock K 3)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) : ChapterB.baumann R = R := by
  have hRK := c.R_le_H.trans c.normalizes_residual
  have hno (W : Subgroup G) (hWR : W ≤ R) (hHW : H ≤ normalizer (W : Set G))
      (hMW : M ≤ normalizer (W : Set G)) : W = ⊥ :=
    c.no_common_normal W hWR ((normal_subgroupOf_iff_le_normalizer
      (hWR.trans (c.R_le_M.trans le_sup_left))).mpr (sup_le hMW hHW))
  have he := h.source_single_block_terminal_equalities c.R_twoGroup H M R le_rfl c.T_le
    c.R_normal hRK c.residual_sup_sylow.symm hno x hx hi hnc
  let := h.elementary
  let : Nontrivial (RankOne.U K) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [h.cubic_module_card hK]
    decide
  let : IsKleinFour (RankOne.U K) := ⟨h.cubic_module_card hK,IsElementaryAbelian.exponent_eq_prime⟩
  have hr := four_twoGroup_centralizer_supplement (RankOne.U K) R
    ((RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom) c.R_twoGroup
    (hRK.trans (normalizer_le_normalizer_characteristic_image K (blockU K)))
    ((h.conjugate_le (c.R_normal hx)).trans inf_le_left) hnc
  apply le_antisymm inf_le_left
  exact hr.le.trans (sup_le (h.conjugate_le (c.R_normal hx)) (he.2.1.le.trans inf_le_left))

theorem cubic_symmetric_factor_from_original
    (c : OriginalHypotheses H M K R R) {F : Type*} [Field F]
    (h : RankOne.Setup R K F) (hK : IsAlternatingBlock K 3)
    (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    Nonempty ((K ⊔ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) ≃*
      Equiv.Perm (Fin 4)) ∧
      (K ⊔ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom) ⊓ centralizer (K : Set G) = ⊥ := by
  let U := RankOne.U K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  have hxN := c.R_normal hx
  have hV := h.conjugate_le hxN
  have hp := h.conjugate_factor_structure hxN hnc
  have hUK : U ≤ K := map_subtype_le _
  have hU : Nat.card U = 4 := h.cubic_module_card hK
  have hVc : Nat.card V = 4 := (card_map_of_injective (MulAut.conj x⁻¹).injective).trans hU
  let := h.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hUV : Nat.card (U ⊓ V : Subgroup G) = 2 := by
    have hn : U ⊓ V ≠ ⊥ := by
      intro he
      have hc := (h.commutator_eq_fixed hxN hnc).2.trans he
      exact hnc (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))
    have h1 : Nat.card (U ⊓ V : Subgroup G) ≠ 1 := fun he => hn (card_eq_one.mp he)
    have h4 : Nat.card (U ⊓ V : Subgroup G) ≠ 4 := by
      intro he
      have hv : U ⊓ V = V := eq_of_le_of_card_ge inf_le_right (by rw [he,hVc])
      apply hnc
      have hf := h.conjugate_fixed_intersection hxN hnc
      rw [hv] at hf
      exact hf.ge.trans inf_le_right
    have hd : Nat.card (U ⊓ V : Subgroup G) ∣ 4 := hU ▸ card_dvd_of_le inf_le_left
    have hb := Nat.le_of_dvd (by decide : 0 < 4) hd
    have hpos : 0 < Nat.card (U ⊓ V : Subgroup G) := Nat.card_pos
    interval_cases Nat.card (U ⊓ V : Subgroup G) <;> norm_num at *
  have hz : (U ⊔ V) ⊓ centralizer (K : Set G) = ⊥ := by
    apply bot_unique
    rintro u ⟨hu,huc⟩
    have hd : u ∈ RankOne.D R K := ⟨(sup_le h.module_le hV) hu,huc⟩
    have hh := hp.2.2.2.1.le ⟨hu,hd⟩
    have hc : (⟨u,hUK hh.1⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro k
      exact Subtype.ext (huc k k.property)
    exact congrArg Subtype.val (hK.center_eq_bot.le hc)
  obtain ⟨e⟩ := hK.equiv_alternatingFour
  exact alternatingFour_extension_structure K U V e hUK
    (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (blockU K)))
    hU hVc (hV.trans h.normalizes) hUV hz

theorem cubic_product_from_original
    (c : OriginalHypotheses H M K R R) {F : Type*} [Field F]
    (h : RankOne.Setup R K F) (hK : IsAlternatingBlock K 3)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    let D := R ⊓ centralizer (K : Set G)
    let E := K ⊔ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom
    D ⊔ E = H ∧ Disjoint D E ∧ D ≤ centralizer (E : Set G) ∧
      Nonempty (H ≃* D × Equiv.Perm (Fin 4)) := by
  let D := R ⊓ centralizer (K : Set G)
  let V := (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom
  let E := K ⊔ V
  have hB := cubic_baumann_eq_original c h hK hi x hx hnc
  have hD : D = RankOne.D R K := by change R ⊓ _ = ChapterB.baumann R ⊓ _; rw [hB]
  have hp := h.conjugate_factor_structure (c.R_normal hx) hnc
  obtain ⟨⟨e⟩,hec⟩ := cubic_symmetric_factor_from_original c h hK x hx hnc
  have hsup : D ⊔ E = H := by
    apply le_antisymm
    · exact sup_le (inf_le_left.trans c.R_le_H)
        (sup_le c.K_le_H ((h.conjugate_le (c.R_normal hx)).trans (inf_le_left.trans c.R_le_H)))
    · rw [←c.residual_sup_sylow]
      apply sup_le (le_sup_of_le_right le_sup_left)
      have hs : RankOne.S R ≤ D ⊔ E := hp.1.le.trans
        (sup_le (sup_le (le_sup_of_le_right ((map_subtype_le _).trans le_sup_left))
          (le_sup_of_le_right le_sup_right)) (hD.symm ▸ le_sup_left))
      simpa only [RankOne.S,hB] using hs
  have hd : Disjoint D E := disjoint_iff.mpr (by
    apply bot_unique
    rintro g ⟨hgD,hgE⟩
    exact hec.le ⟨hgE,hgD.2⟩)
  have hc : D ≤ centralizer (E : Set G) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · exact le_centralizer_iff.mp inf_le_right
    · exact le_centralizer_iff.mp ((hD.le.trans hp.2.1).trans
        (centralizer_le (show V ≤ RankOne.U K ⊔ V from le_sup_right)))
  obtain ⟨a,_,_⟩ := exists_marked_internalProductEquiv H D E hsup hd hc
  exact ⟨hsup,hd,hc,⟨a.trans (MulEquiv.prodCongr (MulEquiv.refl D) e)⟩⟩

theorem cubic_small_core_model_from_original
    (c : OriginalHypotheses H M K R R) {F : Type*} [Field F]
    (h : RankOne.Setup R K F) (hK : IsAlternatingBlock K 3)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G))
    (hsmall : H.pCoreIn 2 = sourceModule K) :
    Nonempty (H ≃* Equiv.Perm (Fin 4)) := by
  let D := R ⊓ centralizer (K : Set G)
  let E := K ⊔ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom
  have hp := cubic_product_from_original c h hK hi x hx hnc
  have hf := rankOne_family_from_original c h hi x hx hnc
  have hDU : D ≤ sourceModule K := by
    rw [←hsmall,hf.2.2.2]
    exact le_sup_right
  have hD : D = ⊥ := bot_unique (by
    intro d hd
    exact hp.2.1.le_bot ⟨hd,(show K ≤ E from le_sup_left) (map_subtype_le _ (hDU hd))⟩)
  have hE : E = H := by
    have hh : D ⊔ E = H := hp.1
    simpa only [hD,bot_sup_eq] using hh
  obtain ⟨e⟩ := (cubic_symmetric_factor_from_original c h hK x hx hnc).1
  exact ⟨(MulEquiv.subgroupCongr hE.symm).trans e⟩

theorem cubic_large_core_model_from_original
    (c : OriginalHypotheses H M K R R) {F : Type*} [Field F]
    (h : RankOne.Setup R K F) (hK : IsAlternatingBlock K 3)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G))
    (hlarge : H.pCoreIn 2 ≠ sourceModule K) :
    Nat.card (R ⊓ centralizer (K : Set G) : Subgroup G) = 2 ∧
      Nonempty (H ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) := by
  let D := R ⊓ centralizer (K : Set G)
  have hb := cubic_baumann_eq_original c h hK hi x hx hnc
  have hD : D = RankOne.D R K := by change R ⊓ _ = ChapterB.baumann R ⊓ _; rw [hb]
  have hf := rankOne_family_from_original c h hi x hx hnc
  have hn : D ≠ ⊥ := by
    intro he
    apply hlarge
    rw [←hf.1,(h.factorization (c.R_normal hx) hnc).core,←hD,he,sup_bot_eq]
    rfl
  have h1 : Nat.card D ≠ 1 := fun he => hn (card_eq_one.mp he)
  have hpos : 0 < Nat.card D := Nat.card_pos
  have hr := cubic_centralizer_rank_from_original c h hK hi x hx hnc
  have hbound : Nat.card D ≤ 2 := hr.2.1
  have hc : Nat.card D = 2 := by omega
  obtain ⟨e⟩ := (cubic_product_from_original c h hK hi x hx hnc).2.2.2
  let a : D ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hc (by simp)
  exact ⟨hc,⟨e.trans (MulEquiv.prodCongr a (MulEquiv.refl _))⟩⟩
end CFSG.Quasithin.ChapterC.Section06
