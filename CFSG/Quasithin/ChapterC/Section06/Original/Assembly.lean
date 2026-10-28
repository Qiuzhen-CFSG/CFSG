module
public import CFSG.Quasithin.ChapterC.Section06.Original.Conclusions
public import CFSG.Quasithin.ChapterC.Section06.Original.ModelOrbit
public import CFSG.Quasithin.ChapterC.Section06.Original.Configuration
public import CFSG.Quasithin.ChapterC.Section06.Original.UniqueModel
public import CFSG.Quasithin.ChapterC.Section06.NaturalGlobal
public import CFSG.Quasithin.ChapterC.Section06.CentralizerRank
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow.MarkedPair
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow.Alternating

/-!
# The original C.6.1 dispatcher

The bare quotient alternatives give both local SQTK and the unique Sylow
maximal overgroup. Original normalizer control constructs C.5.1--2 on an
actual index-two subgroup of Λ. The resulting marked block orbit is either
single or a pair of A₃ blocks, with every module, conjugator, centralizer
identity and Thompson-stability input constructed before applying the
proved branch endpoints. No marked-model premise remains in the theorem.
Source: Aschbacher--Smith C.6.1, printed pp.164--166.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06.Original
open Section05.BlockAnalysis Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {H Λ M : Subgroup G}

theorem natural_conclusion (d : Input H Λ)
    (c : OriginalHypotheses H M ((pResidual 2 H).map H.subtype) (Λ ⊓ H) (Λ ⊓ H))
    {F : Type*} [Field F] (h : RankOne.Setup (Λ ⊓ H) ((pResidual 2 H).map H.subtype) F)
    {n : ℕ} (hK : IsL2EvenBlock ((pResidual 2 H).map H.subtype) n)
    (hMΛ : M ≤ Λ) (hi : (Λ ⊓ H).relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule ((pResidual 2 H).map H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule ((pResidual 2 H).map H.subtype) : Set G)) : Conclusion H Λ := by
  have hn := rankOne_normalizer_from_original c h Λ d.two d.proper d.control hi x hx hnc
  have hg := natural_global_from_original c h hK Λ d.two hMΛ d.control hi x hx hnc
  have hr := natural_centralizer_rank_from_original c h hK hi x hx hnc
  refine ⟨⟨hn.1,hg.2.2.1,hg.2.2.2.1,hn.2.2⟩,Or.inl ⟨n,hK,hr.2.2,?_,hg.1,hg.2.1⟩⟩
  intro y hy hyr
  exact (hg.2.2.2.2 y hy.1 hyr).2.1

theorem cubic_conclusion (d : Input H Λ)
    (c : OriginalHypotheses H M ((pResidual 2 H).map H.subtype) (Λ ⊓ H) (Λ ⊓ H))
    {F : Type*} [Field F] (h : RankOne.Setup (Λ ⊓ H) ((pResidual 2 H).map H.subtype) F)
    (hK : IsAlternatingBlock ((pResidual 2 H).map H.subtype) 3)
    (hMΛ : M ≤ Λ) (hi : (Λ ⊓ H).relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule ((pResidual 2 H).map H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule ((pResidual 2 H).map H.subtype) : Set G)) : Conclusion H Λ := by
  have hg := cubic_global_from_original c h hK Λ d.two d.proper hMΛ d.control hi x hx hnc
  refine ⟨⟨hg.1,hg.2.1,hg.2.2.2.1,fun y hy hyr => (hg.2.2.2.2.1 y hy hyr).1⟩,
    Or.inr (Or.inl ⟨hK,hg.2.2.1,fun y hy hyr => (hg.2.2.2.2.1 y hy hyr).2,?_⟩)⟩
  rcases hg.2.2.2.2.2 with ha | hb
  · exact Or.inl ⟨⟨ha.1,ha.2.1⟩,ha.2.2⟩
  · exact Or.inr hb

theorem alternating_conclusion (d : Input H Λ)
    (c : OriginalHypotheses H M ((pResidual 2 H).map H.subtype) (Λ ⊓ H) (Λ ⊓ H))
    (h : AlternatingPairSetup (Λ ⊓ H) ((pResidual 2 H).map H.subtype) ⊥)
    (hMΛ : M ≤ Λ) (hi : (Λ ⊓ H).relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule ((pResidual 2 H).map H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule ((pResidual 2 H).map H.subtype) : Set G)) : Conclusion H Λ := by
  have hn := alternating_normalizer_from_original c h Λ d.two d.proper d.control hi x hx hnc
  have hg := alternating_global_from_original c h Λ d.two d.proper hMΛ d.control hi x hx hnc
  refine ⟨⟨hn.1,hn.2.1,hn.2.2.1,fun y hy hyr => (hn.2.2.2 y hy hyr).1⟩,
    Or.inr (Or.inr ⟨Or.inl h.block,?_,hg.2.1,?_⟩)⟩
  · intro y hy hyr
    obtain ⟨A,r,hr,hrs,hiA,hA⟩ := (hn.2.2.2 y hy hyr).2
    exact ⟨A,r,hr.1,hrs,hiA,hA⟩
  · rcases hg.2.2 with he | hd
    · exact Or.inl ⟨(congrArg (fun B : Subgroup G => (Λ ⊓ H).relIndex B) he).symm.trans hn.1,
        hg.2.1.symm.trans (congrArg elementaryAbelianMaxJ he)⟩
    · exact Or.inr hd

theorem single_conclusion (d : Input H Λ)
    (c : OriginalHypotheses H M ((pResidual 2 H).map H.subtype) (Λ ⊓ H) (Λ ⊓ H))
    (b : OrbitDecomposition (c.sylow : Subgroup H) ((Λ ⊓ H).subgroupOf H) (pResidual 2 H))
    (hs : b.size = 1) (hMΛ : M ≤ Λ) (hi : (Λ ⊓ H).relIndex M = 2) : Conclusion H Λ := by
  let i : Fin b.size := ⟨0,b.positive⟩
  have he := single_block_eq_residual c b i hs
  obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
  have hnc : ¬ (sourceModule ((b.block i).map H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule ((b.block i).map H.subtype) : Set G) := by
    rw [ambientModule_eq_literal] at hcomm
    exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  have htype := (b.type i).2.of_mulEquiv (equivMapOfInjective (b.block i) H.subtype H.subtype_injective)
  rcases htype with ⟨n,hK⟩ | hK | hK
  · obtain ⟨F,hF,⟨h⟩⟩ := c.rankOne_setup b i (Or.inl ⟨n,hK⟩)
    rw [he] at h hK hnc
    exact natural_conclusion d c h hK hMΛ hi x hx hnc
  · obtain ⟨F,hF,⟨h⟩⟩ := c.rankOne_setup b i (Or.inr hK)
    rw [he] at h hK hnc
    exact cubic_conclusion d c h hK hMΛ hi x hx hnc
  · obtain ⟨P,hP⟩ := c.block_sylow b i
    have hm : (b.block i).map H.subtype =
        ⁅(b.block i).map H.subtype,elementaryAbelianMaxJ (Λ ⊓ H)⁆ := by
      have hh := congrArg (map H.subtype) (b.moved i)
      rw [map_commutator,←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
        map_subgroupOf_eq_of_le c.R_le_H] at hh
      exact hh
    obtain ⟨h⟩ := exists_alternatingPairSetup (Λ ⊓ H) ((b.block i).map H.subtype) ⊥
      c.R_twoGroup hK hm (c.baumann_normalizes_block b i) P hP bot_le (by
        intro r hr
        exact Or.inl (mem_normalizer_iff_map_conj_eq.mp (c.single_block_normalized b i hs hr)))
    rw [he] at h hnc
    exact alternating_conclusion d c h hMΛ hi x hx hnc

theorem paired_conclusion (d : Input H Λ)
    (c : OriginalHypotheses H M ((pResidual 2 H).map H.subtype) (Λ ⊓ H) (Λ ⊓ H))
    (b : OrbitDecomposition (c.sylow : Subgroup H) ((Λ ⊓ H).subgroupOf H) (pResidual 2 H))
    (hs : b.size = 2) (hA3 : ∀ i, IsAlternatingBlock (b.block i) 3)
    (hMΛ : M ≤ Λ) (hi : (Λ ⊓ H).relIndex M = 2) : Conclusion H Λ := by
  let i : Fin b.size := ⟨0,by omega⟩
  let j : Fin b.size := ⟨1,by omega⟩
  have hij : i ≠ j := by intro he; have := congrArg Fin.val he; simp [i,j] at this
  let K₁ := (b.block i).map H.subtype
  let K₂ := (b.block j).map H.subtype
  have hK₁ : IsAlternatingBlock K₁ 3 := RankOne.Solvable.isAlternatingBlock_of_equiv
    (equivMapOfInjective (b.block i) H.subtype H.subtype_injective) (hA3 i)
  have hK₂ : IsAlternatingBlock K₂ 3 := RankOne.Solvable.isAlternatingBlock_of_equiv
    (equivMapOfInjective (b.block j) H.subtype H.subtype_injective) (hA3 j)
  have hjoin : K₁ ⊔ K₂ = (pResidual 2 H).map H.subtype := c.pair_join b i j hij hs
  have hKL : K₂ ≤ centralizer (K₁ : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    change ⁅(b.block j).map H.subtype,(b.block i).map H.subtype⁆ = ⊥
    rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr (b.commute (Ne.symm hij)),Subgroup.map_bot]
  have hpair : ∀ r ∈ Λ ⊓ H, K₁.conjBy r = K₁ ∨ K₁.conjBy r = K₂ :=
    c.pair_action b i j hij hs
  obtain ⟨t,ht,_,he⟩ := c.pair_exchange b i j hij
  have ht' : ∃ t : M, (t : G) ∈ Λ ⊓ H ∧ K₁.conjBy (t : G) = K₂ :=
    ⟨⟨t,c.R_le_M ht⟩,ht,he⟩
  have hfull : (Λ ⊓ H) ⊓ centralizer ((sourceModule K₁ ⊔ sourceModule K₂ : Subgroup G) : Set G) =
      H.pCoreIn 2 := by
    simpa only [ambientModule_eq_literal,K₁,K₂,sourceModule,moduleLayer] using pair_core_centralizer c b i j hij hs
  obtain ⟨F,F',hF,hF',⟨h⟩,⟨h'⟩⟩ := c.rankOne_paired_setups b i j (Or.inr hK₁)
  obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
  have hnc : ¬ (sourceModule K₁).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K₁ : Set G) := by
    rw [ambientModule_eq_literal] at hcomm
    exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  have c' : OriginalHypotheses H M (K₁ ⊔ K₂) (Λ ⊓ H) (Λ ⊓ H) := hjoin.symm ▸ c
  have hn := cubic_pair_normalizer_family_from_original c' h h' hK₁ hK₂ hKL hpair ht' hfull
    Λ d.two d.proper d.control hi x hx hnc
  have hg := cubic_pair_global_from_original c' h h' hK₁ hK₂ hKL hpair ht' hfull
    Λ d.two d.proper hMΛ d.control hi x hx hnc
  have hcore := hn.2.2.1
  rw [hjoin] at hcore
  refine ⟨⟨hn.1,hn.2.1,hcore,fun y hy hyr => (hn.2.2.2 y hy hyr).1⟩,
    Or.inr (Or.inr ⟨Or.inr ⟨K₁,K₂,?_,hK₁,hK₂,hKL,hjoin⟩,
      fun y hy hyr => (hn.2.2.2 y hy hyr).2,hg.2.1,?_⟩)⟩
  · exact fun he => hij (b.injective (map_injective H.subtype_injective he))
  · rcases hg.2.2 with he | hd
    · exact Or.inl ⟨(congrArg (fun B : Subgroup G => (Λ ⊓ H).relIndex B) he).symm.trans hn.1,
        hg.2.1.symm.trans (congrArg elementaryAbelianMaxJ he)⟩
    · exact Or.inr hd

/-- Original C.6.1: all C.5 setup, model and stability inputs are constructed. -/
theorem Input.conclusion (d : Input H Λ) : Conclusion H Λ := by
  obtain ⟨M,hRM,hMΛ,hi,⟨c⟩⟩ := d.exists_c5_configuration (d.models.sylow_unique d.sylow)
  obtain ⟨b⟩ := c.block_decomposition_knownSimple d.models.sqtk
  rcases orbit_alternatives c d.models b with hs | ⟨hs,hA3⟩
  · exact single_conclusion d c b hs hMΛ hi
  · exact paired_conclusion d c b hs hA3 hMΛ hi
end CFSG.Quasithin.ChapterC.Section06.Original
