module
public import CFSG.Quasithin.Chapter2.Section04.CoreSource
public import CFSG.Quasithin.ChapterC.Section06.RankOneSource

/-!
# The original single-block source normalizer

The chosen minimal parabolic supplies C.5.1--2, the actual selected block
is located in the source orbit, and its natural or A₃ type constructs the
marked action. The preceding escape theorem chooses the conjugator. Hence
C.6.1's two-member family and relative normalizer index apply to the literal
Sylow image and O₂(H), with no marking or core-identification premise.

Source: Aschbacher--Smith 2.4.5(3), 2.4.8 and C.6.1, pp.528--529,164--165.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_rankOne_configuration
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (htype : (∃ n, ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n) ∨
      ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3)
    (M₀ : Subgroup G) (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    ∃ _c : OriginalHypotheses d.H M₀ (d.block.map d.H.subtype)
        ((d.S : Subgroup d.H).map d.H.subtype) ((d.S : Subgroup d.H).map d.H.subtype),
      ∃ (F : Type) (_ : Field F),
        ∃ _h : RankOne.Setup ((d.S : Subgroup d.H).map d.H.subtype)
            (d.block.map d.H.subtype) F,
          ∃ x ∈ M₀, ¬ (sourceModule (d.block.map d.H.subtype)).map
            (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule (d.block.map d.H.subtype) : Set G) := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  change R.relIndex M₀ = 2 at hi
  have hn : (R.subgroupOf M₀).Normal := normal_of_index_eq_two hi
  have hMR : M₀ ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM).mp hn
  have hlt : R < M₀ := lt_of_le_of_ne hSM (by
    intro he
    have hh : R.relIndex M₀ = 1 := relIndex_eq_one.mpr he.ge
    omega)
  obtain ⟨c⟩ := d.original_hypotheses T hST M₀ hlt hMT hMR
  rw [hsingle] at c
  obtain ⟨b⟩ := c.block_decomposition_knownSimple (d.local_sqtk hG)
  obtain ⟨i,hiB⟩ := d.selected_block_in_orbit b
  obtain ⟨F,hF,⟨h⟩⟩ := c.rankOne_setup b i (by rw [hiB]; exact htype)
  rw [hiB] at h
  obtain ⟨x,hx,hnc⟩ := d.exists_single_block_noncommuting T hST M₀ hSM hMT hi h.short
    (c.R_le_H.trans c.normalizes_residual)
  exact ⟨c,F,hF,h,x,hx,hnc⟩

theorem MinimalBlockSetup.single_rankOne_normalizer_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (htype : (∃ n, ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n) ∨
      ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    S.relIndex ((T : Subgroup G) ⊓ normalizer (S : Set G)) = 2 ∧
      ChapterB.baumann S = elementaryAbelianMaxJ S ∧
      ∀ x ∈ (T : Subgroup G) ⊓ normalizer (S : Set G), x ∉ S →
        elementaryAbelianMaxJ S = twoCore d.H ⊔
          (twoCore d.H).map (MulAut.conj x⁻¹).toMonoidHom := by
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  obtain ⟨c,F,hF,h,x,hx,hnc⟩ := d.single_rankOne_configuration hG T hST.le hsingle htype
    M₀ hSM hMT hi
  exact ChapterC.Section06.rankOne_normalizer_from_original c h T T.isPGroup' hST
    (fun W hW hWS hHW => lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST.le
      W hW hWS ((normal_subgroupOf_iff_le_normalizer
        (hWS.trans (map_subtype_le _))).mpr hHW)) hi x hx hnc

end CFSG.Quasithin.Chapter2
