module
public import CFSG.Quasithin.Chapter2.Section04.ConjugateSource
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.KnownSimpleSource
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow.Alternating
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow.MarkedPair
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow.Geometry
public import Theory.GroupTheory.SubgroupEnumerationBinary
public import Mathlib.Order.Atoms.Finite
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.C129Complete
/-!
# The original selected-block core in Section 2.4

The actual minimal parabolic satisfies C.5.1--2 by the source normalizer
barrier. The original C.5 producer supplies the residual block orbit and its
rank-one or alternating markings. Guarded block commutation identifies the
selected block in that orbit, so the source calculations preserve the original
L, U₀, Sylow image and centralizer D throughout.

The one- and two-block calculations prove U₀ = O₂(L₀), Q = U₀D and
Q ∈ A(S). The strict Sylow inclusion constructs the required index-two
overgroup; no marking, factorization, block orbit or conjugator is assumed.
The final consumer constructs this entire setup from the original Γₑ₀ and
unique-maximal-two-local hypotheses, using the full known-simple catalogue.

Source: Aschbacher--Smith, Lemma 2.4.5(1),(2),(4), printed p.528,
and C.5.1--7, printed pp.154--160, combined manuscript of 1 March 2004.
The separate C.6.1 applicability assertion in 2.4.5(3), the A₃ branch of
2.4.6 and the subsequent shadow classification remain separate.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- Source 2.4.5(1): the literal C.5.1--2 hypotheses for every proper
normalizing two-overgroup of the selected Sylow. -/
theorem MinimalBlockSetup.original_hypotheses
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ : Subgroup G)
    (hSM : (d.S : Subgroup d.H).map d.H.subtype < M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hn : M₀ ≤ normalizer ((d.S : Subgroup d.H).map d.H.subtype : Set G)) :
    Nonempty (OriginalHypotheses d.H M₀ (d.L0.map d.H.subtype)
      ((d.S : Subgroup d.H).map d.H.subtype) ((d.S : Subgroup d.H).map d.H.subtype)) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  have hSH : S ⊔ d.L0.map d.H.subtype = d.H := by
    rw [sup_comm,d.ambient_L0_sup_sylow]
  have hP : ∃ P : Sylow 2 (S ⊔ d.L0.map d.H.subtype : Subgroup G),
      (P : Subgroup (S ⊔ d.L0.map d.H.subtype : Subgroup G)).map
        (S ⊔ d.L0.map d.H.subtype).subtype = S := by
    rw [hSH]
    exact ⟨d.S,rfl⟩
  obtain ⟨P,hP⟩ := hP
  refine ⟨{
    fitting := generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp d.mem_gammaEvenZero.2)
    sylow := d.S
    sylow_image := rfl
    unique := d.minimal_parabolic.1
    residual := by rw [d.L0_eq_residual]
    R_le := le_rfl
    T_le := hSM.le
    R_normal := hn
    residual_sylow := P
    residual_sylow_image := hP
    no_common_normal := ?_ }⟩
  intro W hWS hnormal
  have hWH : W ≤ d.H := hWS.trans (map_subtype_le _)
  have hnW : M₀ ⊔ d.H ≤ normalizer (W : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (hWS.trans (hSM.le.trans le_sup_left))).mp hnormal
  by_contra hW
  have he := lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST W hW hWS
    ((normal_subgroupOf_iff_le_normalizer hWH).mpr (le_sup_right.trans hnW))
  exact hSM.not_ge ((le_inf hMT (le_sup_left.trans hnW)).trans he.le)

/-- The selected proper local group inherits the full SQTK hypotheses. -/
theorem MinimalBlockSetup.local_sqtk (d : MinimalBlockSetup M)
    {κ : GroupClass} (hG : IsSimpleQTKE κ G) : IsSQTK κ d.H := by
  have hH : d.H ∈ Chapter1.H G :=
    (d.mem_gammaEvenZero.1.elim (fun h => h.1.1) (fun h => h.1)).1
  have hn : IsTwoLocal (normalizer (twoCore d.H : Set G)) :=
    ⟨twoCore d.H,hH,isPGroup_pCoreIn 2 d.H,rfl⟩
  have hs := (hG.twoLocal_sqtk hn).subgroup
    (d.H.subgroupOf (normalizer (twoCore d.H : Set G)))
  exact (IsSQTK.equiv (subgroupOfEquivOfLe (le_normalizer_twoCore d.H))).mp hs

/-- The C.5 orbit contains the original selected block: otherwise every
factor would centralize that nonabelian short block. -/
theorem MinimalBlockSetup.selected_block_in_orbit
    (d : MinimalBlockSetup M)
    {S R : Subgroup d.H}
    (b : OrbitDecomposition S R (pResidual 2 d.H)) :
    ∃ i, b.block i = d.block := by
  classical
  by_contra! hn
  have hf := generalizedFitting_eq_pCore_of_selfCentralizing 2
    (Chapter1.mem_He_iff.mp d.mem_gammaEvenZero.2)
  have hc : (⨆ i, b.block i) ≤ centralizer (d.block : Set d.H) := by
    apply iSup_le
    intro i
    exact commutator_eq_bot_iff_le_centralizer.mp
      (ChapterC.blocks_commute (ChapterC.RankOne.ChiProduct.blockCommutationHypothesis_of_fitting hf)
        (b.type i).1 d.block_type.1 (hn i))
  have hL : d.block ≤ pResidual 2 d.H :=
    le_pResidual_of_isPPerfect d.block d.block_type.1.short.twoPerfect
  rw [b.generate] at hc
  have he : ⁅d.block,d.block⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (hL.trans hc)
  have hu : (ChapterC.blockU d.block).map d.block.subtype ≤ ⁅d.block,d.block⁆ := by
    rw [ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype]
    exact commutator_mono (map_subtype_le _) le_rfl
  rw [he] at hu
  exact d.block_type.1.short.blockU_ne_bot
    (((ChapterC.blockU d.block).map_eq_bot_iff_of_injective d.block.subtype_injective).mp (bot_unique hu))


/-- All the original core conclusions of 2.4.5(2a),(4), on the selected
block. The C.5 source constructs every marking used in the one- and
two-block calculations. -/
theorem MinimalBlockSetup.lemma_2_4_5_2a_4
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ : Subgroup G)
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let U₀ := d.U0.map d.H.subtype
    let D := R ⊓ centralizer (d.L0.map d.H.subtype : Set G)
    d.U0 = d.L0.pCoreIn 2 ∧ twoCore d.H = U₀ ⊔ D ∧
      twoCore d.H ∈ Stellmacher.elementaryAbelianMaxSubgroups R := by
  classical
  let R := (d.S : Subgroup d.H).map d.H.subtype
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hMR : M₀ ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM).mp hn
  have hlt : R < M₀ := lt_of_le_of_ne hSM (by
    intro he
    have h1 : R.relIndex M₀ = 1 := relIndex_eq_one.mpr he.ge
    have h2 : R.relIndex M₀ = 2 := hindex
    omega)
  obtain ⟨c⟩ := d.original_hypotheses T hST M₀ hlt hMT hMR
  obtain ⟨b⟩ := c.block_decomposition_knownSimple (d.local_sqtk hG)
  obtain ⟨i,hi⟩ := d.selected_block_in_orbit b
  have hs : b.size = 1 ∨ b.size = 2 := by
    have := b.positive; have := b.size_le; omega
  rcases hs with hs | hs
  · have hnorm := c.single_block_normalized b i hs
    rw [hi] at hnorm
    rcases c.rankOne_setup_or_alternating b i with ⟨F,_,⟨h⟩⟩ | ha
    · rw [hi] at h
      exact d.rank_one_single_block_core_source T hST M₀ hSM hMT hindex h hnorm
    · obtain ⟨P,hP⟩ := c.block_sylow b i
      have hm : (b.block i).map d.H.subtype =
          ⁅(b.block i).map d.H.subtype,Stellmacher.elementaryAbelianMaxJ R⁆ := by
        have he := congrArg (map d.H.subtype) (b.moved i)
        rw [map_commutator,←Stellmacher.elementaryAbelianMaxJ_map_injective
          d.H.subtype d.H.subtype_injective,map_subgroupOf_eq_of_le c.R_le_H] at he
        exact he
      have hb := c.baumann_normalizes_block b i
      obtain ⟨h⟩ := exists_alternatingPairSetup R ((b.block i).map d.H.subtype) ⊥
        c.R_twoGroup ha hm hb P hP bot_le (by
          intro r hr
          apply Or.inl
          simpa only [hi,MulEquiv.toMonoidHom_eq_coe] using mem_normalizer_iff_map_conj_eq.mp (hnorm hr))
      rw [hi] at h
      exact d.alternating_single_block_core_source T hST M₀ ⊥ hSM hMT hindex h hnorm
  · have hi' := i.isLt
    let j : Fin b.size := ⟨1-i.val,by omega⟩
    have hij : i ≠ j := by
      intro he
      have hv := congrArg Fin.val he
      dsimp only [j] at hv
      omega
    let L₂ := (b.block j).map d.H.subtype
    have hc : L₂ ≤ centralizer (d.block.map d.H.subtype : Set G) := by
      rw [←hi]
      apply commutator_eq_bot_iff_le_centralizer.mp
      rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr
        (b.commute (Ne.symm hij)),Subgroup.map_bot]
    have hperm : ∀ r ∈ R, (d.block.map d.H.subtype).conjBy r = d.block.map d.H.subtype ∨
        (d.block.map d.H.subtype).conjBy r = L₂ := by
      intro r hr
      simpa only [hi] using c.pair_action b i j hij hs r hr
    have hex : ∃ t : M₀, (t : G) ∈ R ∧ (d.block.map d.H.subtype).conjBy (t : G) = L₂ := by
      obtain ⟨t,ht,_,he⟩ := c.pair_exchange b i j hij
      exact ⟨⟨t,hSM ht⟩,ht,by simpa only [hi] using he⟩
    rcases c.rankOne_setup_or_alternating b i with ⟨F,_,⟨h⟩⟩ | ha
    · have ht : (∃ n, ChapterC.IsL2EvenBlock ((b.block i).map d.H.subtype) n) ∨
          ChapterC.IsAlternatingBlock ((b.block i).map d.H.subtype) 3 := by
        rcases h.block with ⟨n,hn,_⟩ | ha
        · exact Or.inl ⟨n,hn⟩
        · exact Or.inr ha
      obtain ⟨F₁,F₂,_,_,⟨h₁⟩,⟨h₂⟩⟩ := c.rankOne_paired_setups b i j ht
      rw [hi] at h₁
      exact d.rank_one_two_block_core_source T hST M₀ L₂ hSM hMT hindex hc hperm h₁ h₂ hex
    · obtain ⟨⟨h₁⟩,⟨h₂⟩⟩ := c.alternating_paired_setups b i j hij hs ha
      rw [hi] at h₁ h₂
      exact d.alternating_two_block_core_source T hST M₀ L₂ hSM hMT hindex h₁ h₂ hex



/-- The strict source Sylow inclusion supplies the required index-two
overgroup; it is not an extra existence hypothesis. -/
theorem MinimalBlockSetup.exists_index_two_overgroup
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G)) :
    ∃ M₀ : Subgroup G,
      (d.S : Subgroup d.H).map d.H.subtype ≤ M₀ ∧ M₀ ≤ (T : Subgroup G) ∧
      ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2 := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  have hR : R.subgroupOf (T : Subgroup G) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    exact fun he => hST.not_ge (subgroupOf_eq_top.mp he)
  obtain ⟨X,hX,_⟩ := exists_covBy_le_of_lt hR
  have hi := Theory.GroupTheory.SubgroupEnumeration.relIndex_two_of_covBy T.isPGroup' hX
  refine ⟨X.map (T : Subgroup G).subtype,?_,map_subtype_le _,?_⟩
  · rw [←map_subgroupOf_eq_of_le hST.le]
    exact map_mono hX.le
  · have he := relIndex_map_map_of_injective (R.subgroupOf (T : Subgroup G)) X
      (T : Subgroup G).subtype_injective
    rw [map_subgroupOf_eq_of_le hST.le] at he
    exact he.trans hi

/-- Source 2.4.5(4) and the core conclusion in (2a), with the index-two
subgroup and all C.5 block/action premises constructed from the original
simple-QTKE hypotheses. -/
theorem MinimalBlockSetup.core_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G)) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let U₀ := d.U0.map d.H.subtype
    let D := R ⊓ centralizer (d.L0.map d.H.subtype : Set G)
    d.U0 = d.L0.pCoreIn 2 ∧ twoCore d.H = U₀ ⊔ D ∧
      twoCore d.H ∈ Stellmacher.elementaryAbelianMaxSubgroups R := by
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  exact d.lemma_2_4_5_2a_4 hG T hST.le M₀ hSM hMT hi

/-- Both clauses of the original 2.4.5(2) on every prescribed index-two
overgroup, with the actual U₀ and centralizer D retained. -/
theorem MinimalBlockSetup.lemma_2_4_5_2
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ : Subgroup G)
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let U₀ := d.U0.map d.H.subtype
    let D := R ⊓ centralizer (d.L0.map d.H.subtype : Set G)
    twoCore d.H = U₀ ⊔ D ∧ twoCore d.H ∈ Stellmacher.elementaryAbelianMaxSubgroups R ∧
      ∀ x ∈ M₀, x ∉ R →
        D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom = ⊥ ∧
          ¬ U₀.map (MulAut.conj x⁻¹).toMonoidHom ≤ twoCore d.H := by
  have hc := d.lemma_2_4_5_2a_4 hG T hST M₀ hSM hMT hindex
  exact ⟨hc.2.1,hc.2.2,fun x hx hxR => d.lemma_2_4_5_2b T hST M₀ hSM hMT hindex x hx hxR⟩


/-- The original nonempty-Γₑ₀ source hypotheses select the actual minimal
parabolic, ambient Sylow and core factorization. C.1.29 and every additional
C.5 block/action premise are discharged. -/
theorem exists_minimalBlockSetup_with_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    {H : Subgroup G} (hH : H ∈ gammaEvenZero (Chapter1.He G) M) :
    ∃ d : MinimalBlockSetup M, d.H ≤ H ∧ ∃ P : Sylow 2 G,
      (P : Subgroup G) ≤ M ∧
      (d.S : Subgroup d.H).map d.H.subtype < (P : Subgroup G) ∧
      d.U0 = d.L0.pCoreIn 2 ∧
      twoCore d.H = d.U0.map d.H.subtype ⊔
        ((d.S : Subgroup d.H).map d.H.subtype ⊓ centralizer (d.L0.map d.H.subtype : Set G)) ∧
      twoCore d.H ∈ Stellmacher.elementaryAbelianMaxSubgroups
        ((d.S : Subgroup d.H).map d.H.subtype) := by
  obtain ⟨d,hd⟩ := exists_minimalBlockSetup hG localC129Input_knownSimple T hTM hunique hH
  obtain ⟨P,hSP⟩ := (d.S.isPGroup'.map d.H.subtype).exists_le_sylow
  have hPM : (P : Subgroup G) ≤ M := (beta_mono d.full_pair.1.1 hSP P.isPGroup').2.1
  have hlt : (d.S : Subgroup d.H).map d.H.subtype < (P : Subgroup G) := by
    apply lt_of_le_of_ne hSP
    intro he
    have hcore : twoCore d.H ≠ ⊥ :=
      (d.mem_gammaEvenZero.1.elim (fun h => h.1.1) (fun h => h.1)).1
    have hPH : (P : Subgroup G) ≤ d.H := he ▸ map_subtype_le _
    have hPMH : (P.subtype hPM : Subgroup M).map M.subtype ≤ d.H := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hPM] using hPH
    have hout : ¬ d.H ≤ M := d.full_pair.1.2.2.2.2
    exact hout (core_overgroup_le_of_sylow T hTM hunique hcore (P.subtype hPM) hPMH)
  exact ⟨d,hd,P,hPM,hlt,d.core_source hG P hlt⟩
end CFSG.Quasithin.Chapter2
