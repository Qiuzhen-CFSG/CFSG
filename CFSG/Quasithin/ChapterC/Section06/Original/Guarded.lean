module
public import CFSG.Quasithin.ChapterC.Section06.Original.Source
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.ChiZeroRank
public import Theory.SpecificGroups.Alternating.FourPairResidual
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The literal type-guarded clauses of C.6.1

A chi-zero residual has three-rank one, so its actual C.5 orbit is single.
This reconstructs the required marking for each supplied natural, A₃ or
A₅ type, without assuming the alternatives are disjoint. A commuting A₃
pair is literally A₄×A₄ and has three-rank two, so it cannot enter the
single-block branches. Thus all original guards in (3)--(4) are retained.
Source: Aschbacher--Smith C.6.1(3),(4),(6), printed pp.164--166.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06.Original
open Section05.BlockAnalysis Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {H Λ M : Subgroup G}

theorem residual_chiZero_single
    (c : OriginalHypotheses H M ((pResidual 2 H).map H.subtype) (Λ ⊓ H) (Λ ⊓ H))
    (b : OrbitDecomposition (c.sylow : Subgroup H) ((Λ ⊓ H).subgroupOf H) (pResidual 2 H))
    (hK : IsChiZeroBlock ((pResidual 2 H).map H.subtype)) : b.size = 1 := by
  have hr := hK.threeRank_le_one
  rw [←primeRank_equiv 3 (equivMapOfInjective (pResidual 2 H) H.subtype H.subtype_injective),
    ResidualCentralizerRank.primeRank_residual (by decide : Nat.Coprime 2 3)] at hr
  have hc := RankOne.ChiProduct.card_le_threeRank
    (RankOne.ChiProduct.blockCommutationHypothesis_of_fitting c.fitting)
    b.block b.injective (fun i => (b.type i).chi)
  simp only [Fintype.card_fin] at hc
  have := b.positive
  omega

theorem Input.rankOne_marking (d : Input H Λ)
    (hK : (∃ n, IsL2EvenBlock ((pResidual 2 H).map H.subtype) n) ∨
      IsAlternatingBlock ((pResidual 2 H).map H.subtype) 3) :
    ∃ M : Subgroup G, ∃ _c : OriginalHypotheses H M ((pResidual 2 H).map H.subtype) (Λ ⊓ H) (Λ ⊓ H),
      M ≤ Λ ∧ (Λ ⊓ H).relIndex M = 2 ∧
      ∃ (F : Type) (_ : Field F), ∃ _h : RankOne.Setup (Λ ⊓ H) ((pResidual 2 H).map H.subtype) F,
        ∃ x ∈ M, ¬ (sourceModule ((pResidual 2 H).map H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
          centralizer (sourceModule ((pResidual 2 H).map H.subtype) : Set G) := by
  obtain ⟨M,_,hMΛ,hi,⟨c⟩⟩ := d.exists_c5_configuration (d.models.sylow_unique d.sylow)
  obtain ⟨b⟩ := c.block_decomposition_knownSimple d.models.sqtk
  have hs := residual_chiZero_single c b (hK.imp id Or.inl)
  let i : Fin b.size := ⟨0,b.positive⟩
  have he := single_block_eq_residual c b i hs
  obtain ⟨F,hF,⟨h⟩⟩ := c.rankOne_setup b i (he.symm ▸ hK)
  obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
  have hnc : ¬ (sourceModule ((b.block i).map H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule ((b.block i).map H.subtype) : Set G) := by
    rw [ambientModule_eq_literal] at hcomm
    exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  rw [he] at h hnc
  exact ⟨M,c,hMΛ,hi,F,hF,h,x,hx,hnc⟩

theorem Input.natural_rank_and_family (d : Input H Λ) {n : ℕ}
    (hK : IsL2EvenBlock ((pResidual 2 H).map H.subtype) n) :
    primeRank 2 ((Λ ⊓ H) ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G) : Subgroup G) ≤ n ∧
      PairFamily H Λ ∧ GlobalIndexTwo H Λ := by
  obtain ⟨M,c,hMΛ,hi,F,hF,h,x,hx,hnc⟩ := d.rankOne_marking (Or.inl ⟨n,hK⟩)
  have hr := natural_centralizer_rank_from_original c h hK hi x hx hnc
  have hg := natural_global_from_original c h hK Λ d.two hMΛ d.control hi x hx hnc
  exact ⟨hr.2.2,fun y hy hyr => (hg.2.2.2.2 y hy.1 hyr).2.1,hg.1,hg.2.1⟩

theorem Input.cubic_rank_and_family (d : Input H Λ)
    (hK : IsAlternatingBlock ((pResidual 2 H).map H.subtype) 3) :
    primeRank 2 ((Λ ⊓ H) ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G) : Subgroup G) ≤ 1 ∧
      PairFamily H Λ ∧
      ((GlobalIndexTwo H Λ ∧ Nonempty (H ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) ∨
        (Nonempty (H ≃* Equiv.Perm (Fin 4)) ∧ (IsDihedralGroup Λ ∨ IsSemidihedralGroup Λ))) := by
  obtain ⟨M,c,hMΛ,hi,F,hF,h,x,hx,hnc⟩ := d.rankOne_marking (Or.inr hK)
  have hg := cubic_global_from_original c h hK Λ d.two d.proper hMΛ d.control hi x hx hnc
  refine ⟨hg.2.2.1,fun y hy hyr => (hg.2.2.2.2.1 y hy hyr).2,?_⟩
  rcases hg.2.2.2.2.2 with ha | hb
  · exact Or.inl ⟨⟨ha.1,ha.2.1⟩,ha.2.2⟩
  · exact Or.inr hb

theorem Input.alternating_branch (d : Input H Λ)
    (hK : IsAlternatingBlock ((pResidual 2 H).map H.subtype) 5) :
    FourFamily H Λ ∧
      elementaryAbelianMaxJ (Λ ⊓ normalizer (Λ ⊓ H : Set G)) = elementaryAbelianMaxJ (Λ ⊓ H) ∧
      (GlobalIndexTwo H Λ ∨ DihedralNormalizer H Λ) := by
  obtain ⟨M,_,hMΛ,hi,⟨c⟩⟩ := d.exists_c5_configuration (d.models.sylow_unique d.sylow)
  obtain ⟨b⟩ := c.block_decomposition_knownSimple d.models.sqtk
  have hs := residual_chiZero_single c b (Or.inr (Or.inr hK))
  let i : Fin b.size := ⟨0,b.positive⟩
  have he := single_block_eq_residual c b i hs
  obtain ⟨P,hP⟩ := c.block_sylow b i
  have hm : (b.block i).map H.subtype =
      ⁅(b.block i).map H.subtype,elementaryAbelianMaxJ (Λ ⊓ H)⁆ := by
    have hh := congrArg (map H.subtype) (b.moved i)
    rw [map_commutator,←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le c.R_le_H] at hh
    exact hh
  obtain ⟨h⟩ := exists_alternatingPairSetup (Λ ⊓ H) ((b.block i).map H.subtype) ⊥
    c.R_twoGroup (he.symm ▸ hK) hm (c.baumann_normalizes_block b i) P hP bot_le (by
      intro r hr
      exact Or.inl (mem_normalizer_iff_map_conj_eq.mp (c.single_block_normalized b i hs hr)))
  obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
  have hnc : ¬ (sourceModule ((b.block i).map H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule ((b.block i).map H.subtype) : Set G) := by
    rw [ambientModule_eq_literal] at hcomm
    exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  rw [he] at h hnc
  have hn := alternating_normalizer_from_original c h Λ d.two d.proper d.control hi x hx hnc
  have hg := alternating_global_from_original c h Λ d.two d.proper hMΛ d.control hi x hx hnc
  refine ⟨?_,hg.2.1,?_⟩
  · intro y hy hyr
    obtain ⟨A,r,hr,hrs,hiA,hA⟩ := (hn.2.2.2 y hy hyr).2
    exact ⟨A,r,hr.1,hrs,hiA,hA⟩
  · rcases hg.2.2 with he | hd
    · exact Or.inl ⟨(congrArg (fun B : Subgroup G => (Λ ⊓ H).relIndex B) he).symm.trans hn.1,
        hg.2.1.symm.trans (congrArg elementaryAbelianMaxJ he)⟩
    · exact Or.inr hd

omit [Finite G] in
theorem CubicPair.model {L : Subgroup G} (h : CubicPair L) :
    Nonempty (L ≃* AlternatingFourPair.Model) := by
  obtain ⟨K₁,K₂,_,h1,h2,hc,he⟩ := h
  have hd : Disjoint K₁ K₂ := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hz : (⟨x,hx.1⟩ : K₁) ∈ center K₁ := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (hc hx.2 y y.property)
    rw [h1.center_eq_bot,mem_bot] at hz
    exact mem_bot.mpr (congrArg Subtype.val hz)
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting K₁ K₂ hd (le_centralizer_iff.mp hc)
  exact ⟨(MulEquiv.subgroupCongr he.symm).trans
    (e.symm.trans ((Classical.choice h1.equiv_alternatingFour).prodCongr
      (Classical.choice h2.equiv_alternatingFour)))⟩

theorem CubicPair.not_chiZero {L : Subgroup G} (h : CubicPair L) : ¬ IsChiZeroBlock L := by
  intro hc
  have hr := hc.threeRank_le_one
  rw [primeRank_equiv 3 (Classical.choice h.model),AlternatingFourPair.pair_threeRank] at hr
  omega

theorem Input.paired_branch (d : Input H Λ)
    (hp : CubicPair ((pResidual 2 H).map H.subtype)) :
    FourFamily H Λ ∧
      elementaryAbelianMaxJ (Λ ⊓ normalizer (Λ ⊓ H : Set G)) = elementaryAbelianMaxJ (Λ ⊓ H) ∧
      (GlobalIndexTwo H Λ ∨ DihedralNormalizer H Λ) := by
  rcases d.conclusion.2 with ⟨n,hn,_⟩ | ⟨h3,_⟩ | ⟨_,hβ⟩
  · exact (hp.not_chiZero (Or.inl ⟨n,hn⟩)).elim
  · exact (hp.not_chiZero (Or.inr (Or.inl h3))).elim
  · exact hβ
end CFSG.Quasithin.ChapterC.Section06.Original
