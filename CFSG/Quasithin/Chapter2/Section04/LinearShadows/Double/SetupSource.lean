module
public import CFSG.Quasithin.Chapter2.Section04.CoreSource
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# The literal paired setup for the double linear source branch

The original C.5 decomposition has two blocks when the selected block is
proper in its Sylow conjugate product. Its transitive action gives the
second block, with the same field exponent, both marked natural actions,
and the noncommuting conjugator in any specified index-two overgroup.

Source: Aschbacher–Smith, 2.4.5 and the opening double-block paragraph of
2.4.7, printed pp.528 and 539, using C.5.3–6.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

structure DoubleLinearSourceSetup (d : MinimalBlockSetup M) (M₀ : Subgroup G) (n : ℕ) where
  original : OriginalHypotheses d.H M₀ (d.L0.map d.H.subtype)
    ((d.S : Subgroup d.H).map d.H.subtype) ((d.S : Subgroup d.H).map d.H.subtype)
  second : Subgroup G
  second_type : ChapterC.IsL2EvenBlock second n
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
  field₁ : Type
  field₂ : Type
  field₁_field : Field field₁
  field₂_field : Field field₂
  marked₁ : @RankOne.Setup G _ ((d.S : Subgroup d.H).map d.H.subtype)
    (d.block.map d.H.subtype) field₁ field₁_field
  marked₂ : @RankOne.Setup G _ ((d.S : Subgroup d.H).map d.H.subtype)
    second field₂ field₂_field
  x : G
  x_mem : x ∈ M₀
  noncommuting : ¬ (sourceModule (d.block.map d.H.subtype)).map
    (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule (d.block.map d.H.subtype) : Set G)

/-- All markings and the escaping element of the original paired linear
configuration are produced from the literal minimal block setup. -/
theorem MinimalBlockSetup.double_linear_configuration
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hpair : d.L0 ≠ d.block) {n : ℕ}
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n)
    (M₀ : Subgroup G) (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    Nonempty (DoubleLinearSourceSetup d M₀ n) := by
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
  have hL₂ : ChapterC.IsL2EvenBlock L₂ n :=
    hL.of_mulEquiv (((MulAut.conj s).subgroupMap (d.block.map d.H.subtype)).trans
      (MulEquiv.subgroupCongr hswap))
  have hne : L₂ ≠ d.block.map d.H.subtype := by
    intro he
    have hb : b.block j = b.block i := map_injective d.H.subtype_injective (he.trans (congrArg (map d.H.subtype) hiB).symm)
    exact hij (b.injective hb).symm
  obtain ⟨F,F',hF,hF',⟨h₁⟩,⟨h₂⟩⟩ := c.rankOne_paired_setups b i j (by
    rw [hiB]
    exact Or.inl ⟨n,hL⟩)
  rw [hiB] at h₁
  obtain ⟨x,hx,hnc⟩ := d.exists_two_block_noncommuting T hST M₀ L₂ hSM hMT hi
    h₁.short h₂.short hc hp ht
  refine ⟨{
    original := c, second := L₂, second_type := hL₂, second_ne := hne,
    commutes := hc, join := ?_, permutes := hp, permutes_second := hp', exchange := ht,
    field₁ := F, field₂ := F', field₁_field := hF, field₂_field := hF',
    marked₁ := h₁, marked₂ := h₂, x := x, x_mem := hx, noncommuting := hnc }⟩
  simpa only [hiB] using c.pair_join b i j hij (by omega)

/-- The two invariant members of the original maximum elementary family
are the actual core and its selected conjugate, and they generate J(S). -/
theorem DoubleLinearSourceSetup.core_pair
    {d : MinimalBlockSetup M} {M₀ : Subgroup G} {n : ℕ}
    (c : DoubleLinearSourceSetup d M₀ n) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let Q := twoCore d.H
    ChapterB.baumann S = Stellmacher.elementaryAbelianMaxJ S ∧
      Stellmacher.elementaryAbelianMaxJ S = Q ⊔ Q.map (MulAut.conj c.x⁻¹).toMonoidHom ∧
      {A ∈ Stellmacher.elementaryAbelianMaxSubgroups S | S ≤ normalizer (A : Set G)} =
        {Q,Q.map (MulAut.conj c.x⁻¹).toMonoidHom} := by
  let := c.field₁_field
  let := c.field₂_field
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let U := sourceModule L ⊔ sourceModule c.second
  let C := ChapterB.baumann S ⊓ centralizer ((L ⊔ c.second : Subgroup G) : Set G)
  let Q := ChapterB.baumann S ⊓ centralizer (U : Set G)
  have hsecond : c.second ≤ d.H := (le_sup_right.trans_eq c.join).trans (map_subtype_le _)
  have hex : ∃ t : M₀, (t : G) ∈ S ∧ L.conjBy (t : G) = c.second := by
    obtain ⟨t,ht,he⟩ := c.exchange
    exact ⟨⟨t,hSM ht⟩,ht,he⟩
  have hh := d.rank_one_two_block_invariant_family T hST M₀ c.second hsecond hSM hMT hi
    c.commutes c.permutes c.permutes_second c.marked₁ c.marked₂ hex c.x c.x_mem c.noncommuting
  have hCore := d.two_block_core_centralizer c.second c.marked₁.short c.marked₂.short
    c.commutes c.permutes c.exchange
  have hclosure := d.two_block_closures c.second c.permutes c.exchange
  have hQle : Q ≤ twoCore d.H := by
    rw [←hCore,hclosure.2]
    exact inf_le_inf inf_le_left le_rfl
  have hCoreMax := (d.rank_one_two_block_core_source T hST M₀ c.second hSM hMT hi
    c.commutes c.permutes c.marked₁ c.marked₂ hex).2.2
  have hQ : Q = twoCore d.H := eq_of_le_of_card_ge hQle
    (hh.1.2.2 _ hCoreMax.1 hCoreMax.2.1)
  have hH : d.H = (L ⊔ c.second) ⊔ S := by
    rw [c.join,d.ambient_L0_sup_sylow]
  have hSN : S ≤ normalizer ((L ⊔ c.second : Subgroup G) : Set G) :=
    c.join.symm ▸ (c.original.R_le_H.trans c.original.normalizes_residual)
  have hp := c.marked₁.two_block_source_product c.marked₂ c.commutes d.H M₀ S hSM
    c.original.R_normal hSN hH (d.no_common_normal_of_index_two T hST M₀ hSM hMT hi)
    c.x c.x_mem hi c.permutes hex c.noncommuting
  have hgen : ChapterB.baumann S = Q ⊔ Q.map (MulAut.conj c.x⁻¹).toMonoidHom := by
    rw [hp.2.2.1]
    rw [←hh.2.2.1]
    have hQU : Q = U ⊔ C := hp.1
    rw [hQU]
    change (U ⊔ U.map (MulAut.conj c.x⁻¹).toMonoidHom) ⊔ C =
      (U ⊔ C) ⊔ (U.map (MulAut.conj c.x⁻¹).toMonoidHom ⊔ C)
    simp only [sup_assoc,sup_left_comm,sup_comm,sup_left_idem]
  refine ⟨hh.2.1,?_,?_⟩
  · rw [←hh.2.1,←hQ]
    exact hgen
  · simpa only [←hQ] using hh.2.2.2

end CFSG.Quasithin.Chapter2
