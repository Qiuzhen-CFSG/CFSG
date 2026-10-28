module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.CubicPairSource
public import CFSG.Quasithin.ChapterC.Section06.CubicPairGlobal
/-!
# The complete global C.6 alternative for the original paired cubic shadow

The actual two-block configuration retains both module actions, their
exchanging element and the escaping conjugate. Original source centralizer
and normalizer control discharge the remaining C.6 inputs. The resulting
four-member family, core factorization and global D₈ alternative concern
the original Sylow image, its normalizer and its Thompson quotient.

Source: Aschbacher--Smith 2.4.5(3), C.6.1, printed pp.528,164--166.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.cubic_pair_global_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpairwise : d.L0 ≠ d.block)
    (hK : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3) :
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let Q := twoCore d.H
    let N₀ := (T : Subgroup G) ⊓ normalizer (R : Set G)
    let S := elementaryAbelianMaxJ R
    let N₁ := (T : Subgroup G) ⊓ normalizer (N₀ : Set G)
    R.relIndex N₀ = 2 ∧ ChapterB.baumann R = S ∧ elementaryAbelianMaxJ N₀ = S ∧
      Q = (d.L0.map d.H.subtype).pCoreIn 2 ⊔
        (R ⊓ centralizer (d.L0.map d.H.subtype : Set G)) ∧
      (∀ y ∈ N₀, y ∉ R →
        S = Q ⊔ Q.map (MulAut.conj y⁻¹).toMonoidHom ∧
        ∃ A : Subgroup G, ∃ r : G,
          r ∈ R ∧ r ∉ S ∧ Q.relIndex A = 2 ∧
          elementaryAbelianMaxSubgroups R =
            {Q,Q.map (MulAut.conj y⁻¹).toMonoidHom,A,A.map (MulAut.conj r⁻¹).toMonoidHom}) ∧
      (N₀ = (T : Subgroup G) ∨ ∃ hn : (S.subgroupOf N₁).Normal,
        letI := hn
        Nonempty ((N₁ ⧸ S.subgroupOf N₁) ≃* DihedralGroup 4) ∧
        ∃ A ∈ elementaryAbelianMaxSubgroups R,
          Q.relIndex A = 2 ∧ Nat.card R ≤ Nat.card ((T : Subgroup G) ⊓
            normalizer ((Q ⊔ A : Subgroup G) : Set G) : Subgroup G)) := by
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
  have hcontrol (W : Subgroup G) (hW : W ≠ ⊥)
      (hWR : W ≤ (d.S : Subgroup d.H).map d.H.subtype)
      (hHW : d.H ≤ normalizer (W : Set G)) : (T : Subgroup G) ⊓ normalizer (W : Set G) =
        (d.S : Subgroup d.H).map d.H.subtype :=
    lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST.le
      W hW hWR ((normal_subgroupOf_iff_le_normalizer
        (hWR.trans (map_subtype_le _))).mpr hHW)
  have hn := ChapterC.Section06.cubic_pair_normalizer_family_from_original c h h' hK hL hKL
    hpair ht hfull T T.isPGroup' hST hcontrol hi x hx hnc
  have hg := ChapterC.Section06.cubic_pair_global_from_original c h h' hK hL hKL hpair ht hfull
    T T.isPGroup' hST hMT hcontrol hi x hx hnc
  refine ⟨hn.1,hn.2.1,hg.2.1,?_,hn.2.2.2,hg.2.2⟩
  rw [hjoin]
  exact hn.2.2.1

end CFSG.Quasithin.Chapter2
