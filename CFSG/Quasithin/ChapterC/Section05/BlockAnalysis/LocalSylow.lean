module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.KnownSimpleSource
/-!
# The C.5.6 one-block obstruction with the local Sylow subgroup

The Sylow calculations in C.5.6 only require the source Sylow to be
Sylow in M₀. The actual C.5.3 orbit, its constructed rank-one/A₅ markings
and noncommuting conjugate therefore rule out a single block before any
ambient Sylow assumption. In three-rank at most one the two-block outcome
is impossible. This is the precise local-Sylow use in the proof of 4.3.1.

Source: Aschbacher–Smith C.5.3–6, printed pp.154–158, and 4.3.1, p.613.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
open ConjugateSource ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {H M K R T : Subgroup G}

theorem OriginalHypotheses.two_blocks_of_localSylow
    (d : OriginalHypotheses H M K R T)
    (b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))
    (P : Sylow 2 M) (hP : (P : Subgroup M).map M.subtype = T) : b.size = 2 := by
  have hs : b.size = 1 ∨ b.size = 2 := by
    have := b.positive; have := b.size_le; omega
  apply hs.resolve_left
  intro hs
  let i : Fin b.size := ⟨0,b.positive⟩
  have hn := d.single_block_normalized b i hs
  obtain ⟨x,hx,hm⟩ := d.exists_noncommuting_module b i
  have hu : U ((b.block i).map H.subtype) = ambientModule (b.block i) :=
    (ambientModule_eq_literal _).symm
  have hnc : ¬ (U ((b.block i).map H.subtype)).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (U ((b.block i).map H.subtype) : Set G) := by
    rw [hu]
    intro hc
    exact hm (by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr hc)
  rcases d.rankOne_setup_or_alternating b i with ⟨F,_,⟨h⟩⟩ | ha
  · exact h.sylow_not_normalizes_block M d.R_normal P hx hnc (hP ▸ hn)
  · obtain ⟨Q,hQ⟩ := d.block_sylow b i
    have hmoved : (b.block i).map H.subtype =
        ⁅(b.block i).map H.subtype,elementaryAbelianMaxJ R⁆ := by
      have he := congrArg (map H.subtype) (b.moved i)
      rw [map_commutator,←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
        map_subgroupOf_eq_of_le d.R_le_H] at he
      exact he
    obtain ⟨h⟩ := exists_alternatingPairSetup R ((b.block i).map H.subtype) ⊥
      d.R_twoGroup ha hmoved (d.baumann_normalizes_block b i) Q hQ bot_le
      (fun r hr => Or.inl (mem_normalizer_iff_map_conj_eq.mp (hn (d.R_le hr))))
    exact AlternatingQuotient.sylow_not_normalizes_block h (Or.inl (d.R_le.trans hn))
      M d.R_normal P x hx hnc (hP ▸ hn)

theorem OriginalHypotheses.false_of_localSylow_threeRank_one
    (d : OriginalHypotheses H M K R T)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hr : primeRank 3 H ≤ 1)
    (P : Sylow 2 M) (hP : (P : Subgroup M).map M.subtype = T) : False := by
  obtain ⟨b⟩ := d.block_decomposition_knownSimple hH
  have hs := d.two_blocks_of_localSylow b P hP
  have hb := (RankOne.ChiProduct.card_le_threeRank
    (RankOne.ChiProduct.blockCommutationHypothesis_of_fitting d.fitting)
    b.block b.injective (fun i => (b.type i).chi)).trans hr
  simp only [Fintype.card_fin] at hb
  omega
end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
