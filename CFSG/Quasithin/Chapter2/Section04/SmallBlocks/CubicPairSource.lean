module
public import CFSG.Quasithin.Chapter2.Section04.CoreSource
public import CFSG.Quasithin.ChapterC.Section06.RankOnePairSource
/-!
# The original two-A₃ configuration and normalizer

The full known-simple C.5 decomposition locates the selected cubic block.
The nonsingle residual forces exactly two factors, and the source Sylow
orbit constructs the second block and its exchanging element. Both marked
actions, the escaping conjugate and the original core-centralizer identity
are proved internally. Thus the C.6 four-family and relative normalizer
conclusions concern the literal selected Sylow and O₂(H).

Source: Aschbacher--Smith 2.4.5(3), C.6.1(1),(4),(5), pp.528,164--165.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.cubic_pair_configuration
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hpairwise : d.L0 ≠ d.block)
    (hK : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3)
    (M₀ : Subgroup G) (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let K := d.block.map d.H.subtype
    ∃ L : Subgroup G,
      ∃ _c : OriginalHypotheses d.H M₀ (K ⊔ L) R R,
      ∃ (F F' : Type) (_ : Field F) (_ : Field F'),
        ∃ _h : RankOne.Setup R K F, ∃ _h' : RankOne.Setup R L F',
          ChapterC.IsAlternatingBlock L 3 ∧ L ≤ centralizer (K : Set G) ∧
          d.L0.map d.H.subtype = K ⊔ L ∧
          (∀ r ∈ R, K.conjBy r = K ∨ K.conjBy r = L) ∧
          (∃ t : M₀, (t : G) ∈ R ∧ K.conjBy (t : G) = L) ∧
          ∃ x ∈ M₀, ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
            centralizer (sourceModule K : Set G) := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let K := d.block.map d.H.subtype
  change R.relIndex M₀ = 2 at hi
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hi
  have hMR : M₀ ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM).mp hn
  have hlt : R < M₀ := lt_of_le_of_ne hSM (by
    intro he
    have hh : R.relIndex M₀ = 1 := relIndex_eq_one.mpr he.ge
    omega)
  obtain ⟨c⟩ := d.original_hypotheses T hST M₀ hlt hMT hMR
  obtain ⟨b⟩ := c.block_decomposition_knownSimple (d.local_sqtk hG)
  obtain ⟨i,hiB⟩ := d.selected_block_in_orbit b
  have hs : b.size = 2 := by
    have hp := b.positive
    have hle := b.size_le
    have hn : b.size ≠ 1 := by
      intro he
      have hnorm := c.single_block_normalized b i he
      rw [hiB] at hnorm
      have hh := (d.single_block_closures hnorm).1
      exact hpairwise (map_injective d.H.subtype_injective hh)
    omega
  have hi' := i.isLt
  let j : Fin b.size := ⟨1-i.val,by omega⟩
  have hij : i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    dsimp only [j] at hv
    omega
  let L := (b.block j).map d.H.subtype
  have hc : L ≤ centralizer (K : Set G) := by
    change (b.block j).map d.H.subtype ≤ centralizer (d.block.map d.H.subtype : Set G)
    rw [←hiB]
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr (b.commute (Ne.symm hij)),Subgroup.map_bot]
  have hperm : ∀ r ∈ R, K.conjBy r = K ∨ K.conjBy r = L := by
    intro r hr
    simpa only [hiB] using c.pair_action b i j hij hs r hr
  obtain ⟨t,ht,_,he⟩ := c.pair_exchange b i j hij
  have htL : K.conjBy t = L := by simpa only [hiB] using he
  have hL : ChapterC.IsAlternatingBlock L 3 := by
    let e := ((MulAut.conj t).subgroupMap K).trans (MulEquiv.subgroupCongr htL)
    exact ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv e hK
  obtain ⟨F,F',hF,hF',⟨h⟩,⟨h'⟩⟩ := c.rankOne_paired_setups b i j
    (Or.inr (by rw [hiB]; exact hK))
  rw [hiB] at h
  have hjoin : d.L0.map d.H.subtype = K ⊔ L := by
    simpa only [hiB] using (c.pair_join b i j hij hs).symm
  have ht' : ∃ t ∈ R, K.conjBy t = L := ⟨t,ht,htL⟩
  obtain ⟨x,hx,hnc⟩ := d.exists_two_block_noncommuting T hST M₀ L hSM hMT hi
    hK.2.1 hL.2.1 hc hperm ht'
  rw [hjoin] at c
  exact ⟨L,c,F,F',hF,hF',h,h',hL,hc,hjoin,hperm,⟨⟨t,hSM ht⟩,ht,htL⟩,x,hx,hnc⟩

theorem MinimalBlockSetup.cubic_pair_normalizer_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpairwise : d.L0 ≠ d.block)
    (hK : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let K := d.block.map d.H.subtype
    let Q := twoCore d.H
    R.relIndex ((T : Subgroup G) ⊓ normalizer (R : Set G)) = 2 ∧
      ChapterB.baumann R = elementaryAbelianMaxJ R ∧
      (∀ y ∈ (T : Subgroup G) ⊓ normalizer (R : Set G), y ∉ R →
        elementaryAbelianMaxJ R = Q ⊔ Q.map (MulAut.conj y⁻¹).toMonoidHom) ∧
      ∃ L : Subgroup G, ∃ x ∈ (T : Subgroup G),
        ChapterC.IsAlternatingBlock L 3 ∧ d.L0.map d.H.subtype = K ⊔ L ∧
        elementaryAbelianMaxSubgroups R =
          {Q,Q.map (MulAut.conj x⁻¹).toMonoidHom,
            (sourceModule K ⊔ (sourceModule L).map (MulAut.conj x⁻¹).toMonoidHom) ⊔
              (R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)),
            ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ⊔ sourceModule L) ⊔
              (R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G))} := by
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  obtain ⟨L,c,F,F',hF,hF',h,h',hL,hKL,hjoin,hpair,ht,x,hx,hnc⟩ :=
    d.cubic_pair_configuration hG T hST.le hpairwise hK M₀ hSM hMT hi
  have ht' : ∃ t ∈ (d.S : Subgroup d.H).map d.H.subtype,
      (d.block.map d.H.subtype).conjBy t = L := by
    obtain ⟨t,ht,he⟩ := ht
    exact ⟨t,ht,he⟩
  have hcl := d.two_block_closures L hpair ht'
  have hfull := d.two_block_core_centralizer L h.short h'.short hKL hpair ht'
  rw [hcl.2] at hfull
  have hf := ChapterC.Section06.rankOne_pair_family_from_original c h h' hKL hpair ht hfull hi x hx hnc
  have hn := ChapterC.Section06.rankOne_pair_normalizer_from_original c h h' hKL hpair ht hfull
    T T.isPGroup' hST
    (fun W hW hWR hHW => lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST.le
      W hW hWR ((normal_subgroupOf_iff_le_normalizer
        (hWR.trans (map_subtype_le _))).mpr hHW)) hi x hx hnc
  exact ⟨hn.1,hn.2.1,hn.2.2,L,x,hMT hx,hL,hjoin,hf.2.2.2.2.2.2⟩

end CFSG.Quasithin.Chapter2
