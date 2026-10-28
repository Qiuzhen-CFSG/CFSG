module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryAlphaCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalElementarySource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.AlphaSecondKernel

/-!
# The elementary source's second kernels on both vertex orbits

The literal elementary full-Borel quotient supplies both local catalogues
and a linear beta marking. Its proved four-walk transitivity constructs
the escaping path needed by the Chapter 11 kernel calculation. Conjugation
then gives the full alpha radius-two kernel, the beta radius-two radical,
and the full radius-three kernel at every vertex. The beta radical is
central elementary in the intrinsic local group by the commuting critical
center theorem. No escaping path or local catalogue is an extra premise.

ElementaryActorCentralCore applies these identities to the actual opposite
four-path actor, preserving the original universal covering. The full
local kernel and its two-core remain distinct.
Source: DGS, Groups and Graphs (1985), (11.6)--(11.7), pp.172--175;
the r=4 core argument in (14.9), p.215.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open Reduction NoncommutingProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "G₀" => Reduction.G₀ L S
variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (helem : ∃ hN : (((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))))

include h hc hb hcomm helem


private theorem elementary_base_second_kernels :
    ballKernel F (base F false) 2 = ⊥ ∧
      ballKernel F (base F true) 3 = ⊥ ∧
      (ballKernel F (base F true) 2).pCoreIn 2 = Z F (base F true) := by
  let d := reducedFullEarlierLocalTheorems h
  let ea := (d.localGroup (base F false)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eb := (d.localGroup (base F true)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have Ma := (original_borel_elementary_alpha_model h hc hb helem).of_equiv eqa
  have Mb := (original_borel_elementary_beta_model h helem).of_equiv eqb
  obtain ⟨m,hm,mark⟩ := original_borel_elementary_linear_beta h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem
  have ht := original_linear_beta_four_walk_transitive h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem) hm mark
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,p,hp,hpv⟩ := source_exists_escaping_four_walk
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    d hc hb hcomm Ma Mb ht
  exact source_full_second_kernels_on_escaping_path
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    d hc hb hcomm hbc hac Ma Mb g hga hgb hesc (ht (g • c)) p hp
    (by rw [hpv]; simp) (by rw [hpv]; simp) (by rw [hpv]; simp)
    (by rw [hpv]; simp) (by rw [hpv]; simp)

/-- The actual radius-two radical is trivial on alpha and central in the
intrinsic local group on beta. Every radius-three kernel is trivial. -/
theorem original_elementary_second_kernel_structure (v : Vertex F) :
    (v.type=false → ballKernel F v 2=⊥) ∧
      (v.type=true → (ballKernel F v 2).pCoreIn 2=Z F v) ∧
      (ballKernel F v 2).pCoreIn 2 ≤ omegaCenterIn (graphLocalGroup F v) ∧
      ballKernel F v 3=⊥ := by
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let d := reducedFullEarlierLocalTheorems h
  obtain ⟨hα,hβ,hZ⟩ := elementary_base_second_kernels h hc hb hcomm helem
  have hcentral : Z F (base F true)=omegaCenterIn (graphLocalGroup F (base F true)) :=
    critical_end_center_of_commuting F (reduced_triple h).generate
      (fun w => (source_Z_Q_U (reduced_triple h) w).1)
      (fun w => (source_Z_Q_U (reduced_triple h) w).2) hc hcomm
      (d.localGroup (base F true)) (d.sylow_or_center (base F true))
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  have ht0 (hv : v.type=false) : ballKernel F v 2=⊥ := by
    rw [←hg,ballKernel_translate,hv,hα,Subgroup.map_bot]
  have ht1 (hv : v.type=true) : (ballKernel F v 2).pCoreIn 2=Z F v := by
    rw [←hg,ballKernel_translate,Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (MulAut.conj g).injective,hv,hZ,←Z_translate]
  refine ⟨ht0,ht1,?_,?_⟩
  · cases hv : v.type
    · rw [ht0 hv]
      exact (pCoreIn_le 2 ⊥).trans bot_le
    · rw [ht1 hv,←hg,hv,Z_translate,hcentral]
      rw [show graphLocalGroup F (g • base F true)=
        (graphLocalGroup F (base F true)).map (MulAut.conj g).toMonoidHom from graphLocalGroup_conjugate (reduced_triple h) g _]
      exact (NilesRankOneKernel.omegaCenterIn_map_injective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective _).le
  · cases hv : v.type
    · exact bot_unique ((ballKernel_antitone F v (by decide : 2≤3)).trans (ht0 hv).le)
    · rw [←hg,ballKernel_translate,hv,hβ,Subgroup.map_bot]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
