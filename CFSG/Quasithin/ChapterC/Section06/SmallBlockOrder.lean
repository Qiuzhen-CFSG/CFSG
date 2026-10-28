module
public import CFSG.Quasithin.ChapterC.Section06.Original.Guarded
public import CFSG.Quasithin.ChapterC.Section06.SmallBlockCenter

/-!
# Sylow orders for the small original C.6 blocks

The original C.5 block orbit supplies the actual marked action. For an A₅
block or a pair of A₃ blocks, its module has order sixteen and the successive
core and Baumann indices are four and two. The center estimate bounds the
remaining centralizer by four, giving Sylow order at most 2⁹. In the single
A₃ case, the recognized S₄ or C₂ × S₄ model gives order at most sixteen.

The dispatcher uses the source block decomposition and constructs all marked
action data; it does not assume a quotient model. Its Chapter 14 consumer is
`source_lemma_14_6_9_small_blocks`.
Source: Aschbacher–Smith, C.5.6, C.6.1 and 14.6.9, printed pp.156–159,
164–166 and 1025 (refs/quasithin.pdf).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {H M K L R : Subgroup G}

private theorem card_join_le (A B : Subgroup G) (hn : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) ≤ Nat.card A * Nat.card B := by
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B hn
  have hp := Nat.card_pos (α := ↥(A ⊓ B))
  nlinarith

omit [Finite G] in
private theorem count (A B : Subgroup G) (h : A ≤ B) :
    Nat.card A * A.relIndex B = Nat.card B := by
  simpa only [relIndex_bot_left] using relIndex_mul_relIndex (⊥ : Subgroup G) A B bot_le h

private theorem alternating_sylow_card
    (c : OriginalHypotheses H M K R R) (h : AlternatingPairSetup R K L)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    Nat.card R ≤ 128 * Nat.card (R ⊓ centralizer (K : Set G) : Subgroup G) := by
  let D := R ⊓ centralizer (K : Set G)
  let S := ChapterB.baumann R
  let Q := H.pCoreIn 2
  have hf := alternating_family_from_original c h hi x hx hnc
  have hidx := (alternating_action_from_original c h hi x hx hnc).1
  have hJS : ChapterB.baumann R = elementaryAbelianMaxJ R := hf.2.2.2.2.1
  rw [←hJS] at hidx
  have hQS : Q ≤ S := by
    change H.pCoreIn 2 ≤ ChapterB.baumann R
    rw [←hf.1, h.core]
    exact inf_le_left
  have hQi : Q.relIndex S = 4 := by
    change (H.pCoreIn 2).relIndex (ChapterB.baumann R) = 4
    rw [←hf.1,h.core,inf_relIndex_left]
    exact h.baumann_action_index
  have hprod : Q ≤ sourceModule K ⊔ D := by
    rw [show Q = (K ⊔ ChapterB.baumann R).pCoreIn 2 from hf.1.symm,h.product]
    exact sup_le_sup le_rfl (inf_le_inf_right _ inf_le_left)
  have hDU : D ≤ centralizer (sourceModule K : Set G) :=
    inf_le_right.trans (centralizer_le (map_subtype_le _))
  have hQcard := (card_le_of_le hprod).trans
    (card_join_le (sourceModule K) D (hDU.trans (Subgroup.centralizer_le_normalizer _)))
  rw [h.module_card] at hQcard
  have h1 := count Q S hQS
  have h2 := count S R inf_le_left
  rw [hQi] at h1
  rw [hidx] at h2
  dsimp only [D] at hQcard
  omega

private theorem cubic_pair_sylow_card
    (c : OriginalHypotheses H M (K ⊔ L) R R)
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (h' : RankOne.Setup R L F')
    (hK : IsAlternatingBlock K 3) (hL : IsAlternatingBlock L 3)
    (hKL : L ≤ centralizer (K : Set G))
    (hpair : ∀ r ∈ R, K.conjBy r = K ∨ K.conjBy r = L)
    (ht : ∃ t : M, (t : G) ∈ R ∧ K.conjBy (t : G) = L)
    (hfull : R ⊓ centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) = H.pCoreIn 2)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    Nat.card R ≤ 128 * Nat.card (R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G) : Subgroup G) := by
  let D := R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  let U := sourceModule K ⊔ sourceModule L
  let S := ChapterB.baumann R
  let Q := H.pCoreIn 2
  have hf := rankOne_pair_family_from_original c h h' hKL hpair ht hfull hi x hx hnc
  have hidx := (cubic_pair_index_from_original c h h' hK hL hKL hpair ht hfull hi x hx hnc).1
  have hQS : Q ≤ S := le_sup_left.trans hf.2.2.2.2.1.ge
  let σ := h.paired_cubic_action h' hK hL
  have hk : σ.ker = Q.subgroupOf S := by
    rw [h.paired_cubic_kernel h' hK hL]
    ext s
    change (s : G) ∈ centralizer (sourceModule K ⊔ sourceModule L : Subgroup G) ↔ (s : G) ∈ H.pCoreIn 2
    rw [←hfull]
    exact (and_iff_right ((show S ≤ R from inf_le_left) s.property)).symm
  have hQi : Q.relIndex S = 4 := by
    change (Q.subgroupOf S).index = 4
    rw [←hk,index_ker,(h.paired_cubic_range h' hK hL hKL M R x hx (c.R_normal hx) hi hpair ht hnc).1]
    exact ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.actor_card
  have hRK := c.R_le_H.trans c.normalizes_residual
  have hH : H = (K ⊔ L) ⊔ R := c.residual_sup_sylow.symm
  have hno (W : Subgroup G) (hWR : W ≤ R) (hHW : H ≤ normalizer (W : Set G))
      (hMW : M ≤ normalizer (W : Set G)) : W = ⊥ :=
    c.no_common_normal W hWR ((normal_subgroupOf_iff_le_normalizer
      (hWR.trans (c.R_le_M.trans le_sup_left))).mpr (sup_le hMW hHW))
  have he := h.source_two_block_terminal_equalities h' c.R_twoGroup hKL H M R le_rfl
    c.T_le c.R_normal hRK hH hno x hx hi hpair ht hnc
  have hprod : Q = U ⊔ D := by
    change H.pCoreIn 2 = (sourceModule K ⊔ sourceModule L) ⊔ _
    have he' : (K ⊔ L).pCoreIn 2 = sourceModule K ⊔ sourceModule L := he.1
    rw [←he']
    exact hf.2.1
  have hUle : U ≤ K ⊔ L := sup_le_sup (map_subtype_le _) (map_subtype_le _)
  have hDU : D ≤ centralizer (U : Set G) := inf_le_right.trans (centralizer_le hUle)
  have hUU : sourceModule L ≤ centralizer (sourceModule K : Set G) :=
    (map_subtype_le _).trans (hKL.trans (centralizer_le (map_subtype_le _)))
  have hUc : Nat.card U ≤ 16 := by
    have hc := card_join_le (sourceModule K) (sourceModule L)
      (hUU.trans (Subgroup.centralizer_le_normalizer _))
    have hcK : Nat.card (sourceModule K) = 4 := h.cubic_module_card hK
    have hcL : Nat.card (sourceModule L) = 4 := h'.cubic_module_card hL
    rw [hcK, hcL] at hc
    exact hc
  have hQcard : Nat.card Q ≤ 16 * Nat.card D := by
    rw [hprod]
    exact (card_join_le U D (hDU.trans (Subgroup.centralizer_le_normalizer _))).trans
      (Nat.mul_le_mul_right _ hUc)
  have h1 := count Q S hQS
  have h2 := count S R inf_le_left
  rw [hQi] at h1
  rw [hidx] at h2
  dsimp only [D] at hQcard
  omega

theorem cubic_sylow_card_from_original
    (c : OriginalHypotheses H M K R R) {F : Type*} [Field F]
    (h : RankOne.Setup R K F) (hK : IsAlternatingBlock K 3)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) : Nat.card R ≤ 16 := by
  have he := Nat.card_congr (equivMapOfInjective (c.sylow : Subgroup H)
    H.subtype H.subtype_injective).toEquiv
  rw [c.sylow_image] at he
  rw [←he,c.sylow.card_eq_multiplicity]
  by_cases hsmall : H.pCoreIn 2 = sourceModule K
  · obtain ⟨e⟩ := cubic_small_core_model_from_original c h hK hi x hx hnc hsmall
    have hc : Nat.card H = 24 := by
      rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
      norm_num
    rw [hc, show (24 : ℕ) = 2 ^ 3 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  · obtain ⟨_,⟨e⟩⟩ := cubic_large_core_model_from_original c h hK hi x hx hnc hsmall
    have hc : Nat.card H = 48 := by
      rw [Nat.card_congr e.toEquiv,Nat.card_prod,Nat.card_perm,Nat.card_fin]
      norm_num [Nat.card_eq_fintype_card]
    rw [hc, show (48 : ℕ) = 2 ^ 4 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]

open Original

private theorem residual_chiZero_single_general
    (c : OriginalHypotheses H M K R R)
    (b : OrbitDecomposition (c.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))
    (hK : IsChiZeroBlock K) : b.size = 1 := by
  have hR : R ⊓ H = R := inf_eq_left.mpr c.R_le_H
  have hthm := @residual_chiZero_single G _ _ H R M
  rw [hR,c.residual] at hthm
  exact hthm c b hK

/-- The A₅ and paired A₃ cases excluded in original 14.6.9. All C.6 data
are constructed from its original four hypotheses. -/
theorem small_block_sylow_card_from_original
    (c : OriginalHypotheses H M K R R) (hsq : IsSQTK KnownSimple.IsKnownSimple H)
    (hi : R.relIndex M = 2)
    (htype : IsAlternatingBlock K 3 ∨ IsAlternatingBlock K 5 ∨ CubicPair K) :
    Nat.card R ≤ 2 ^ 9 := by
  obtain ⟨b⟩ := c.block_decomposition_knownSimple hsq
  rcases htype with hK | hK | hp
  · have hs := residual_chiZero_single_general c b (Or.inr (Or.inl hK))
    let i : Fin b.size := ⟨0,b.positive⟩
    have he := single_block_eq_residual c b i hs
    obtain ⟨F,hF,⟨h⟩⟩ := c.rankOne_setup b i (Or.inr (he.symm ▸ hK))
    obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
    have hnc : ¬ (sourceModule ((b.block i).map H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
        centralizer (sourceModule ((b.block i).map H.subtype) : Set G) := by
      rw [ambientModule_eq_literal] at hcomm
      exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
    rw [he] at h hnc
    exact (cubic_sylow_card_from_original c h hK hi x hx hnc).trans (by norm_num)
  · have hs := residual_chiZero_single_general c b (Or.inr (Or.inr hK))
    let i : Fin b.size := ⟨0,b.positive⟩
    have he := single_block_eq_residual c b i hs
    obtain ⟨P,hP⟩ := c.block_sylow b i
    have hm : (b.block i).map H.subtype =
        ⁅(b.block i).map H.subtype,elementaryAbelianMaxJ R⁆ := by
      have hh := congrArg (map H.subtype) (b.moved i)
      rw [map_commutator,←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
        map_subgroupOf_eq_of_le c.R_le_H] at hh
      exact hh
    obtain ⟨h⟩ := exists_alternatingPairSetup R ((b.block i).map H.subtype) ⊥
      c.R_twoGroup (he.symm ▸ hK) hm (c.baumann_normalizes_block b i) P hP bot_le (by
        intro r hr
        exact Or.inl (mem_normalizer_iff_map_conj_eq.mp (c.single_block_normalized b i hs hr)))
    obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
    have hnc : ¬ (sourceModule ((b.block i).map H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
        centralizer (sourceModule ((b.block i).map H.subtype) : Set G) := by
      rw [ambientModule_eq_literal] at hcomm
      exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
    rw [he] at h hnc
    have hD := (alternating_block_center_index_from_original c h hi x hx hnc).2.2
    have hR := alternating_sylow_card c h hi x hx hnc
    omega
  · by_cases hs : b.size = 1
    · let i : Fin b.size := ⟨0,b.positive⟩
      have he := single_block_eq_residual c b i hs
      have hc := (b.type i).2.of_mulEquiv (equivMapOfInjective (b.block i) H.subtype H.subtype_injective)
      rw [he] at hc
      exact (hp.not_chiZero hc).elim
    · have hs : b.size = 2 := by have := b.positive; have := b.size_le; omega
      let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
      let e := Classical.choice hp.model
      let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      have hA3 (i : Fin b.size) : IsAlternatingBlock (b.block i) 3 := by
        have hb : (b.block i).map H.subtype ≤ K := by
          exact (map_mono ((le_iSup b.block i).trans b.generate.le)).trans_eq c.residual
        let f : b.block i →* K := (H.subtype.comp (b.block i).subtype).codRestrict K
          (fun g => hb (mem_map_of_mem H.subtype g.property))
        have hinj : Function.Injective f := fun a b he =>
          Subtype.ext (Subtype.ext (congrArg (fun k : K => (k : G)) he))
        let : Group.IsSolvable (b.block i) := Group.isSolvable_of_isSolvable_injective (f := f) hinj
        exact chiZero_cubic_of_solvable (b.type i).2
      let i : Fin b.size := ⟨0,by omega⟩
      let j : Fin b.size := ⟨1,by omega⟩
      have hij : i ≠ j := by intro he; have := congrArg Fin.val he; simp [i,j] at this
      let K₁ := (b.block i).map H.subtype
      let K₂ := (b.block j).map H.subtype
      have hK₁ : IsAlternatingBlock K₁ 3 := RankOne.Solvable.isAlternatingBlock_of_equiv
        (equivMapOfInjective (b.block i) H.subtype H.subtype_injective) (hA3 i)
      have hK₂ : IsAlternatingBlock K₂ 3 := RankOne.Solvable.isAlternatingBlock_of_equiv
        (equivMapOfInjective (b.block j) H.subtype H.subtype_injective) (hA3 j)
      have hjoin : K₁ ⊔ K₂ = K := c.pair_join b i j hij hs
      have hKL : K₂ ≤ centralizer (K₁ : Set G) := by
        apply commutator_eq_bot_iff_le_centralizer.mp
        change ⁅(b.block j).map H.subtype,(b.block i).map H.subtype⁆ = ⊥
        rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr (b.commute (Ne.symm hij)),Subgroup.map_bot]
      have hpair : ∀ r ∈ R, K₁.conjBy r = K₁ ∨ K₁.conjBy r = K₂ :=
        c.pair_action b i j hij hs
      obtain ⟨t,ht,_,he⟩ := c.pair_exchange b i j hij
      have ht' : ∃ t : M, (t : G) ∈ R ∧ K₁.conjBy (t : G) = K₂ :=
        ⟨⟨t,c.R_le_M ht⟩,ht,he⟩
      have hfull : R ⊓ centralizer ((sourceModule K₁ ⊔ sourceModule K₂ : Subgroup G) : Set G) =
          H.pCoreIn 2 := by
        simpa only [ambientModule_eq_literal,K₁,K₂,sourceModule,moduleLayer] using pair_core_centralizer c b i j hij hs
      obtain ⟨F,F',hF,hF',⟨h⟩,⟨h'⟩⟩ := c.rankOne_paired_setups b i j (Or.inr hK₁)
      obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
      have hnc : ¬ (sourceModule K₁).map (MulAut.conj x⁻¹).toMonoidHom ≤
          centralizer (sourceModule K₁ : Set G) := by
        rw [ambientModule_eq_literal] at hcomm
        exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
      have c' : OriginalHypotheses H M (K₁ ⊔ K₂) R R := hjoin.symm ▸ c
      have hD := (cubic_pair_block_center_index_from_original c' h h' hK₁ hK₂ hKL hpair ht' hi x hx hnc).2.2
      have hR := cubic_pair_sylow_card c' h h' hK₁ hK₂ hKL hpair ht' hfull hi x hx hnc
      omega

end CFSG.Quasithin.ChapterC.Section06
