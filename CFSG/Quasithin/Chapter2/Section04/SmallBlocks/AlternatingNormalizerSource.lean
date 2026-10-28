module
public import CFSG.Quasithin.Chapter2.Section04.CoreSource
public import CFSG.Quasithin.ChapterC.Section06.AlternatingSource
/-!
# The original A₅ four-family and Sylow normalizer

The selected block and full known-simple C.5 decomposition construct its
actual permutation action. The source escape supplies the conjugator, and
2.4.4 supplies the normalizer obstruction. Thus the C.6 core, four-family,
Thompson span and relative normalizer index apply to the original S and Q.

Source: Aschbacher--Smith 2.4.5(3), C.6.1(1),(4),(5), pp.528,164--165.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_configuration
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (htype : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (M₀ : Subgroup G) (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    ∃ _c : OriginalHypotheses d.H M₀ (d.block.map d.H.subtype)
        ((d.S : Subgroup d.H).map d.H.subtype) ((d.S : Subgroup d.H).map d.H.subtype),
      ∃ _h : AlternatingPairSetup ((d.S : Subgroup d.H).map d.H.subtype)
          (d.block.map d.H.subtype) ⊥,
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
  obtain ⟨P,hP⟩ := c.block_sylow b i
  have hm : (b.block i).map d.H.subtype =
      ⁅(b.block i).map d.H.subtype,elementaryAbelianMaxJ R⁆ := by
    have he := congrArg (map d.H.subtype) (b.moved i)
    rw [map_commutator,←elementaryAbelianMaxJ_map_injective
      d.H.subtype d.H.subtype_injective,map_subgroupOf_eq_of_le c.R_le_H] at he
    exact he
  have hb := c.baumann_normalizes_block b i
  have hnorm := c.R_le_H.trans c.normalizes_residual
  obtain ⟨h⟩ := exists_alternatingPairSetup R ((b.block i).map d.H.subtype) ⊥
    c.R_twoGroup (by rw [hiB]; exact htype) hm hb P hP bot_le (by
      intro r hr
      apply Or.inl
      simpa only [hiB,MulEquiv.toMonoidHom_eq_coe] using mem_normalizer_iff_map_conj_eq.mp (hnorm hr))
  rw [hiB] at h
  obtain ⟨x,hx,hnc⟩ := d.exists_single_block_noncommuting T hST M₀ hSM hMT hi htype.2.1 hnorm
  exact ⟨c,h,x,hx,hnc⟩

theorem MinimalBlockSetup.single_alternating_normalizer_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (htype : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let K := d.block.map d.H.subtype
    S.relIndex ((T : Subgroup G) ⊓ normalizer (S : Set G)) = 2 ∧
      ChapterB.baumann S = elementaryAbelianMaxJ S ∧
      twoCore d.H = K.pCoreIn 2 ⊔ (S ⊓ centralizer (K : Set G)) ∧
      ∀ x ∈ (T : Subgroup G) ⊓ normalizer (S : Set G), x ∉ S →
        elementaryAbelianMaxJ S = twoCore d.H ⊔
          (twoCore d.H).map (MulAut.conj x⁻¹).toMonoidHom ∧
        ∃ A : Subgroup G, ∃ r : G,
          r ∈ S ⊓ K ∧ r ∉ elementaryAbelianMaxJ S ∧ (twoCore d.H).relIndex A = 2 ∧
          elementaryAbelianMaxSubgroups S =
            {twoCore d.H,(twoCore d.H).map (MulAut.conj x⁻¹).toMonoidHom,
              A,A.map (MulAut.conj r⁻¹).toMonoidHom} := by
  obtain ⟨M₀,hSM,hMT,hi⟩ := d.exists_index_two_overgroup T hST
  obtain ⟨c,h,x,hx,hnc⟩ := d.single_alternating_configuration hG T hST.le hsingle htype
    M₀ hSM hMT hi
  exact ChapterC.Section06.alternating_normalizer_from_original c h T T.isPGroup' hST
    (fun W hW hWS hHW => lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST.le
      W hW hWS ((normal_subgroupOf_iff_le_normalizer
        (hWS.trans (map_subtype_le _))).mpr hHW)) hi x hx hnc

end CFSG.Quasithin.Chapter2
