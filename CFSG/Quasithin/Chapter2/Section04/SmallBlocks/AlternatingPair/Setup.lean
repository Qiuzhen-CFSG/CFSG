module
public import CFSG.Quasithin.Chapter2.Section04.CoreSource
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# The original paired alternating-five configuration

The actual C.5 decomposition has two blocks when the selected block is
proper in its Sylow conjugate product. Its transitive Sylow action supplies
the second block, both marked A₅ actions and the escaping conjugator in a
specified index-two overgroup. These are the literal inputs used in the
Frattini-normalizer argument of source 2.4.25, printed pp.541–543.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

structure AlternatingPairSourceSetup (d : MinimalBlockSetup M) (M₀ : Subgroup G) where
  original : OriginalHypotheses d.H M₀ (d.L0.map d.H.subtype)
    ((d.S : Subgroup d.H).map d.H.subtype) ((d.S : Subgroup d.H).map d.H.subtype)
  second : Subgroup G
  second_type : ChapterC.IsAlternatingBlock second 5
  second_ne : second ≠ d.block.map d.H.subtype
  commutes : second ≤ centralizer (d.block.map d.H.subtype : Set G)
  join : d.block.map d.H.subtype ⊔ second = d.L0.map d.H.subtype
  permutes : ∀ s ∈ (d.S : Subgroup d.H).map d.H.subtype,
    (d.block.map d.H.subtype).conjBy s = d.block.map d.H.subtype ∨
      (d.block.map d.H.subtype).conjBy s = second
  permutes_second : ∀ s ∈ (d.S : Subgroup d.H).map d.H.subtype,
    second.conjBy s = second ∨ second.conjBy s = d.block.map d.H.subtype
  exchange : ∃ s ∈ (d.S : Subgroup d.H).map d.H.subtype,
    (d.block.map d.H.subtype).conjBy s = second
  marked₁ : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
    (d.block.map d.H.subtype) second
  marked₂ : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
    second (d.block.map d.H.subtype)
  x : G
  x_mem : x ∈ M₀
  noncommuting : ¬ (sourceModule (d.block.map d.H.subtype)).map
    (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule (d.block.map d.H.subtype) : Set G)

/-- All markings and the escaping element of the original paired alternating
configuration are produced from the literal minimal block setup. -/
theorem MinimalBlockSetup.alternating_pair_configuration
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (hL : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (M₀ : Subgroup G) (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    Nonempty (AlternatingPairSourceSetup d M₀) := by
  classical
  let S := (d.S : Subgroup d.H).map d.H.subtype
  change S.relIndex M₀ = 2 at hi
  have hn : (S.subgroupOf M₀).Normal := normal_of_index_eq_two hi
  have hMS : M₀ ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM).mp hn
  have hlt : S < M₀ := lt_of_le_of_ne hSM (by
    intro he
    have hh : S.relIndex M₀ = 1 := relIndex_eq_one.mpr he.ge
    omega)
  obtain ⟨c⟩ := d.original_hypotheses T hST M₀ hlt hMT hMS
  obtain ⟨b⟩ := c.block_decomposition_knownSimple (d.local_sqtk hG)
  obtain ⟨i,hiB⟩ := d.selected_block_in_orbit b
  have hs : b.size = 2 := by
    have hp := b.positive
    have hb := b.size_le
    by_contra hh
    have h1 : b.size = 1 := by omega
    have he : (⨆ j, b.block j) = d.block := by
      apply le_antisymm
      · apply iSup_le
        intro j
        have hji : j = i := Fin.ext (by have := i.isLt; have := j.isLt; omega)
        rw [hji,hiB]
      · rw [←hiB]
        exact le_iSup _ i
    have hres := b.generate
    rw [he,←d.L0_eq_residual] at hres
    exact hpair hres.symm
  let j : Fin b.size := ⟨1-i.val,by have := i.isLt; omega⟩
  have hij : i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    have hb := i.isLt
    dsimp only [j] at hv
    omega
  let L₂ := (b.block j).map d.H.subtype
  have hc : L₂ ≤ centralizer (d.block.map d.H.subtype : Set G) := by
    rw [←hiB]
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr
      (b.commute (Ne.symm hij)),Subgroup.map_bot]
  have hp : ∀ s ∈ S, (d.block.map d.H.subtype).conjBy s = d.block.map d.H.subtype ∨
      (d.block.map d.H.subtype).conjBy s = L₂ := by
    intro s hs
    simpa only [hiB] using c.pair_action b i j hij (by omega) s hs
  have hp' : ∀ s ∈ S, L₂.conjBy s = L₂ ∨ L₂.conjBy s = d.block.map d.H.subtype := by
    intro s hs
    simpa only [hiB] using c.pair_action b j i hij.symm (by omega) s hs
  obtain ⟨s,hs,_,he⟩ := c.pair_exchange b i j hij
  have hswap : (d.block.map d.H.subtype).conjBy s = L₂ := by simpa only [hiB] using he
  have ht : ∃ s ∈ S, (d.block.map d.H.subtype).conjBy s = L₂ := ⟨s,hs,hswap⟩
  have hL₂ : ChapterC.IsAlternatingBlock L₂ 5 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv (((MulAut.conj s).subgroupMap (d.block.map d.H.subtype)).trans
      (MulEquiv.subgroupCongr hswap)) hL
  have hne : L₂ ≠ d.block.map d.H.subtype := by
    intro he
    have hb : b.block j = b.block i := map_injective d.H.subtype_injective (he.trans (congrArg (map d.H.subtype) hiB).symm)
    exact hij (b.injective hb).symm
  obtain ⟨⟨h₁⟩,⟨h₂⟩⟩ := c.alternating_paired_setups b i j hij (by omega) (by
    rw [hiB]
    exact hL)
  rw [hiB] at h₁ h₂
  obtain ⟨x,hx,hnc⟩ := d.exists_two_block_noncommuting T hST M₀ L₂ hSM hMT hi
    h₁.block.2.1 h₂.block.2.1 hc hp ht
  refine ⟨{
    original := c, second := L₂, second_type := hL₂, second_ne := hne,
    commutes := hc, join := ?_, permutes := hp, permutes_second := hp', exchange := ht,
    marked₁ := h₁, marked₂ := h₂, x := x, x_mem := hx, noncommuting := hnc }⟩
  simpa only [hiB] using c.pair_join b i j hij (by omega)

end CFSG.Quasithin.Chapter2
