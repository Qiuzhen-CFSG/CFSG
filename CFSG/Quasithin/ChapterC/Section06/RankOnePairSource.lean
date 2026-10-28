module
public import CFSG.Quasithin.ChapterC.Section06.RankOneSource
public import Theory.GroupTheory.PGroup.InvariantThompsonPairNormalizer
/-!
# The original paired rank-one family in C.6.1

The actual C.5 two-block setups preserve both modules and the exchanging
Sylow element. Their terminal centralizer equalities identify the marked
core with O₂(H). The complete family consists of the original and conjugate
cores together with the two mixed module products. Its invariant core pair
then gives index two in N_Λ(R) and every outside conjugate Thompson span.

The preceding original module-centralizer identity remains explicit here;
the literal Chapter 2 consumer discharges it from the selected-block source.
Source: Aschbacher--Smith C.6.1(1),(4),(5), printed pp.164--165.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {H M K L R : Subgroup G}

theorem rankOne_pair_family_from_original
    (c : OriginalHypotheses H M (K ⊔ L) R R)
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (h' : RankOne.Setup R L F')
    (hKL : L ≤ centralizer (K : Set G))
    (hpair : ∀ r ∈ R, K.conjBy r = K ∨ K.conjBy r = L)
    (ht : ∃ t : M, (t : G) ∈ R ∧ K.conjBy (t : G) = L)
    (hfull : R ⊓ centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) = H.pCoreIn 2)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    let Q := H.pCoreIn 2
    let S := ChapterB.baumann R
    let D := R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
    let U₁ := sourceModule K
    let U₂ := sourceModule L
    let V₁ := U₁.map (MulAut.conj x⁻¹).toMonoidHom
    let V₂ := U₂.map (MulAut.conj x⁻¹).toMonoidHom
    S = elementaryAbelianMaxJ R ∧ Q = (K ⊔ L).pCoreIn 2 ⊔ D ∧
      (frattini D).map D.subtype = ⊥ ∧ D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom = ⊥ ∧
      S = Q ⊔ Q.map (MulAut.conj x⁻¹).toMonoidHom ∧
      {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} =
        {Q,Q.map (MulAut.conj x⁻¹).toMonoidHom} ∧
      elementaryAbelianMaxSubgroups R =
        {Q,Q.map (MulAut.conj x⁻¹).toMonoidHom,(U₁ ⊔ V₂) ⊔ D,(V₁ ⊔ U₂) ⊔ D} := by
  have hRK := c.R_le_H.trans c.normalizes_residual
  have hH : H = (K ⊔ L) ⊔ R := c.residual_sup_sylow.symm
  have hno (W : Subgroup G) (hWR : W ≤ R) (hHW : H ≤ normalizer (W : Set G))
      (hMW : M ≤ normalizer (W : Set G)) : W = ⊥ :=
    c.no_common_normal W hWR ((normal_subgroupOf_iff_le_normalizer
      (hWR.trans (c.R_le_M.trans le_sup_left))).mpr (sup_le hMW hHW))
  have he := h.source_two_block_terminal_equalities h' c.R_twoGroup hKL H M R le_rfl
    c.T_le c.R_normal hRK hH hno x hx hi hpair ht hnc
  have hp := h.two_block_source_product h' hKL H M R c.T_le c.R_normal hRK hH hno
    x hx hi hpair ht hnc
  have hf := h.two_block_invariant_family h' hKL H M R c.T_le c.R_normal hRK hH hno
    x hx hi hpair ht hnc
  have hcore : RankOne.S R ⊓ centralizer ((RankOne.U K ⊔ RankOne.U L : Subgroup G) : Set G) = H.pCoreIn 2 :=
    he.2.1.symm.trans hfull
  have hD := he.2.2.symm
  have hprod : H.pCoreIn 2 = (sourceModule K ⊔ sourceModule L) ⊔
      (R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)) := by
    rw [←hcore,hp.1,hD]
    rfl
  have hop : ((sourceModule K ⊔ sourceModule L).map (MulAut.conj x⁻¹).toMonoidHom) ⊔
      (R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)) = (H.pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [←hD,←hcore]
    exact hf.2.2.1
  refine ⟨hf.2.1,?_,?_,?_,?_,?_,?_⟩
  · rw [he.1]
    exact hprod
  · have hh := hp.2.2.2.1
    rw [hD] at hh
    exact hh
  · simpa only [hD] using hp.2.2.2.2.1
  · have hh := hp.2.2.1
    change ChapterB.baumann R = _ at hh
    rw [hD] at hh
    change ChapterB.baumann R = H.pCoreIn 2 ⊔ (H.pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom
    rw [←hop,hprod,hh]
    ac_rfl
  · simpa only [hcore] using hf.2.2.2
  · have hfamily (A : Subgroup G) := h.two_block_family h' hKL H M R c.T_le c.R_normal hRK hH hno
      x hx hi hpair ht hnc A
    ext A
    rw [←baumann_maxFamily R]
    have hh := hfamily A
    dsimp only at hh
    rw [hh]
    change (∃ a ∈ ({sourceModule K,(sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom} : Set (Subgroup G)),
      ∃ b ∈ ({sourceModule L,(sourceModule L).map (MulAut.conj x⁻¹).toMonoidHom} : Set (Subgroup G)),
      A = (a ⊔ b) ⊔ (ChapterB.baumann R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G))) ↔ _
    rw [hD,←hop,hprod,Subgroup.map_sup]
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,exists_eq_or_imp,exists_eq_left]
    tauto

theorem rankOne_pair_normalizer_from_original
    (c : OriginalHypotheses H M (K ⊔ L) R R)
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (h' : RankOne.Setup R L F')
    (hKL : L ≤ centralizer (K : Set G))
    (hpair : ∀ r ∈ R, K.conjBy r = K ∨ K.conjBy r = L)
    (ht : ∃ t : M, (t : G) ∈ R ∧ K.conjBy (t : G) = L)
    (hfull : R ⊓ centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) = H.pCoreIn 2)
    (Λ : Subgroup G) (hΛ : IsPGroup 2 Λ) (hRΛ : R < Λ)
    (hcontrol : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ R → H ≤ normalizer (W : Set G) →
      Λ ⊓ normalizer (W : Set G) = R)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    R.relIndex (Λ ⊓ normalizer (R : Set G)) = 2 ∧
      ChapterB.baumann R = elementaryAbelianMaxJ R ∧
      ∀ y ∈ Λ ⊓ normalizer (R : Set G), y ∉ R →
        elementaryAbelianMaxJ R = H.pCoreIn 2 ⊔
          (H.pCoreIn 2).map (MulAut.conj y⁻¹).toMonoidHom := by
  have hf := rankOne_pair_family_from_original c h h' hKL hpair ht hfull hi x hx hnc
  have hQ : H.pCoreIn 2 ≠ ⊥ := by
    intro he
    let := h.elementary
    have hUC : sourceModule K ≤ centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) :=
      le_centralizer_iff.mpr (sup_le (le_centralizer (RankOne.U K))
        ((map_subtype_le _).trans (hKL.trans (centralizer_le (map_subtype_le _)))))
    have hu := (le_inf (h.module_le.trans inf_le_left) hUC).trans hfull.le
    exact moduleLayer_ne_bot h.short (bot_unique (he ▸ hu))
  have hQR : H.pCoreIn 2 ≤ R := by
    simpa only [c.sylow_image] using pCoreIn_le_sylow H c.sylow
  have hnQ : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hp := twoGroup_normalizer_index_two_of_invariant_maxFamily_pair Λ R (H.pCoreIn 2)
    ((H.pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom) hΛ hRΛ hf.2.2.2.2.2.1
    (hcontrol _ hQ hQR hnQ) (hf.1.symm.trans hf.2.2.2.2.1)
  exact ⟨hp.1,hf.1,hp.2⟩

end CFSG.Quasithin.ChapterC.Section06
