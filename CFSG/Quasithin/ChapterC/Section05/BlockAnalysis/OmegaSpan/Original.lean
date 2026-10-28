module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OmegaSpan.Seeds
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow.Orbit
public import Theory.GroupTheory.PairNormalizerIndex

/-!
# The omega-center span for the original C.5 block orbit

For one block, the full original Sylow normalizes it and its noncentral
fixed seed generates U. For two blocks, the literal module stabilizer has
index two. An outside element carries U to the distinct commuting block,
so the central diagonal construction supplies the same full-module span.
All normalization, index, movement and commutation inputs come from the
original enumerated C.5.3 orbit; no new source setup is assumed.

Source: Aschbacher–Smith C.5.3–4, printed p.155, and the omega-center span
used in the C.5.8–13 reduction, printed pp.160–163.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
variable {H M K R T : Subgroup G}
variable (d : OriginalHypotheses H M K R T)
variable (b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))

theorem OriginalHypotheses.module_le_omega_span (i : Fin b.size) :
    ambientModule (b.block i) ≤ conjugateSpanBy (omegaOneCenterAmbient T) H := by
  let B := (b.block i).map H.subtype
  have hB : IsChiZeroBlock B := chiZero_equiv
    ((b.block i).equivMapOfInjective H.subtype H.subtype_injective) (b.type i).2
  have hu : U B = ambientModule (b.block i) := (ambientModule_eq_literal _).symm
  have hT : IsPGroup 2 T := d.sylow_image ▸ d.sylow.isPGroup'.map H.subtype
  have hUT : U B ≤ T := hu ▸ (d.module_le_R b i).trans d.R_le
  by_cases hs : b.size = 1
  · have hTB := d.single_block_normalized b i hs
    obtain ⟨u,huB,huΩ,hunc⟩ := chiZero_noncentral_omega_seed B T hB hT hUT hTB
    have hseed : ¬ U B ⊓ omegaOneCenterAmbient T ≤ centralizer (B : Set G) :=
      fun hh => hunc (hh ⟨huB,huΩ⟩)
    rw [←hu]
    exact (NormalizerControl.omega_span_of_noncentral_fixed B T hB.chi.short hseed).trans
      (conjugateSpanBy_mono le_rfl (map_subtype_le _))
  · have hs2 : b.size = 2 := by have := b.positive;have := b.size_le;omega
    have hi := i.isLt
    let j : Fin b.size := ⟨1-i.val,by omega⟩
    have hij : i ≠ j := by
      intro he
      have hh := congrArg Fin.val he
      dsimp only [j] at hh
      omega
    obtain ⟨t,ht,hmove⟩ := d.exists_moving_module b i hs2
    have hpair := d.module_pair b i j hij hs2
    have hswap := (hpair t ht).resolve_left hmove
    let S := T ⊓ normalizer (U B : Set G)
    have hUS : U B ≤ S := le_inf hUT (U B).le_normalizer
    have hSK : S ≤ normalizer (B : Set G) := by
      simpa only [S,hu] using d.module_stabilizer_le_block_normalizer b i
    have hindex : S.relIndex T = 2 := by
      simpa only [S,hu,inf_relIndex_left] using
        normalizer_relIndex_eq_two_of_pair T (ambientModule (b.block i))
          (ambientModule (b.block j)) hpair t ht hmove
    have htS : t ∉ S := fun hh => hmove
      (hu ▸ mem_normalizer_iff_map_conj_eq.mp hh.2)
    have hcentral : ambientModule (b.block j) ≤ centralizer (B : Set G) := by
      rintro v ⟨w,hw,rfl⟩ k ⟨a,ha,rfl⟩
      exact congrArg H.subtype (b.commute (Ne.symm hij) (moduleLayer_le _ hw) a ha)
    rw [←hu]
    exact paired_block_omega_span H T S B hB hT inf_le_left hindex d.T_le_H
      (map_subtype_le _) hUS hSK t ht htS (by rw [hu,hswap];exact hcentral)

/-- The full product of the original module layers lies in the same omega span. -/
theorem OriginalHypotheses.module_join_le_omega_span :
    (⨆ i, ambientModule (b.block i)) ≤ conjugateSpanBy (omegaOneCenterAmbient T) H :=
  iSup_le (fun i => d.module_le_omega_span b i)

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
