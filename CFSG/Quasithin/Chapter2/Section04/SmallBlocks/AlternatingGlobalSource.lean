module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingActionSource
public import CFSG.Quasithin.ChapterC.Section06.AlternatingGlobal
/-!
# The original A₅ shadow satisfies the global C.6 alternative

The selected block constructs the C.5 configuration, actual action and
escaping conjugator. The original 2.4.4 barrier supplies normalizer control.
Combining the relative normalizer theorem with Thompson stability and the
faithful four-family action proves the global alternative on the literal
Sylow group, its normalizer, and the quotient by its Thompson subgroup.

Source: Aschbacher--Smith 2.4.5(3), C.6.1(1),(6), pp.528,164--166.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_global_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (htype : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let N₀ := (T : Subgroup G) ⊓ normalizer (R : Set G)
    let S := elementaryAbelianMaxJ R
    let N₁ := (T : Subgroup G) ⊓ normalizer (N₀ : Set G)
    R.relIndex N₀ = 2 ∧ ChapterB.baumann R = S ∧ elementaryAbelianMaxJ N₀ = S ∧
      (N₀ = (T : Subgroup G) ∨ ∃ hn : (S.subgroupOf N₁).Normal,
        letI := hn
        Nonempty ((N₁ ⧸ S.subgroupOf N₁) ≃* DihedralGroup 4) ∧
        ∃ A ∈ elementaryAbelianMaxSubgroups R,
          (twoCore d.H).relIndex A = 2 ∧
          Nat.card R ≤ Nat.card ((T : Subgroup G) ⊓
            normalizer ((twoCore d.H ⊔ A : Subgroup G) : Set G) : Subgroup G)) := by
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  obtain ⟨c,h,x,hx,hnc⟩ := d.single_alternating_configuration hG T hST.le hsingle htype
    M₀ hSM hMT hi
  have hcontrol (W : Subgroup G) (hW : W ≠ ⊥)
      (hWR : W ≤ (d.S : Subgroup d.H).map d.H.subtype)
      (hHW : d.H ≤ normalizer (W : Set G)) : (T : Subgroup G) ⊓ normalizer (W : Set G) =
        (d.S : Subgroup d.H).map d.H.subtype :=
    lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST.le
      W hW hWR ((normal_subgroupOf_iff_le_normalizer
        (hWR.trans (map_subtype_le _))).mpr hHW)
  have hn := ChapterC.Section06.alternating_normalizer_from_original c h T T.isPGroup' hST
    hcontrol hi x hx hnc
  have hg := ChapterC.Section06.alternating_global_from_original c h T T.isPGroup' hST hMT
    hcontrol hi x hx hnc
  exact ⟨hn.1,hn.2.1,hg.2.1,hg.2.2⟩

end CFSG.Quasithin.Chapter2
