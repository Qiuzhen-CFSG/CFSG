module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PathBorel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OmegaGeneration

/-!
# The full opposite omega actor on a two-edge path

An edge-normalizer element is corrected by the middle edge Sylow to fix
both path endpoints. That Sylow centralizes every elementary quotient
actor. The terminal normalizer therefore makes the original actor
invariant under the full beta Sylow normalizer. Rank-one omega generation
then identifies its image with the entire Sylow omega-center, uniformly
for every source model, including both unitary covers.

Source: DGS, *Groups and Graphs* (1985), 8.6--8.7, printed p.140.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A nonzero elementary terminal actor in the middle core fills the
beta quotient omega-center when the middle edge action is transitive. -/
theorem source_path_normalized_omega_image
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {beta mid a' : Vertex (family P)}
    (hbm : (graph (family P)).Adj beta mid)
    (ham : (graph (family P)).Adj a' mid) (hne : beta ≠ a')
    (Mb : IsRankOneModel (d.localGroup beta ⧸ pCore 2 (d.localGroup beta)))
    (Mm : IsRankOneModel (d.localGroup mid ⧸ pCore 2 (d.localGroup mid)))
    (hnd : ¬ Nonempty ((d.localGroup mid ⧸ pCore 2 (d.localGroup mid)) ≃* DihedralGroup 5))
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAL : A ≤ d.localGroup beta) (hAQ : A ≤ Q (family P) mid)
    (hescape : ¬ A ≤ Q (family P) beta)
    (hn : stabilizer (family P) a' ≤ normalizer (A : Set G)) :
    ∃ R : Sylow 2 (d.localGroup beta),
      (A.subgroupOf (d.localGroup beta)).map (QuotientGroup.mk' (pCore 2 (d.localGroup beta))) =
        omegaCenterIn ((R : Subgroup (d.localGroup beta)).map
          (QuotientGroup.mk' (pCore 2 (d.localGroup beta)))) := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup beta
  let q := QuotientGroup.mk' (pCore 2 L)
  let I := (A.subgroupOf L).map q
  let : Finite L := Finite.of_injective (inclusion (d.local_le beta)) (inclusion_injective _)
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.map q
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hbm
  let S := R.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  have hAR : A.subgroupOf L ≤ R := by
    intro x hx
    have hh : (x : G) ∈ (R : Subgroup L).map L.subtype := by
      rw [hR]
      have hi := Noncommuting.graph_Q_le_edgeCore h hbm.symm (hAQ hx)
      change (x : G) ∈ _ at hi
      simpa only [inf_comm] using hi
    obtain ⟨y,hy,he⟩ := hh
    exact (Subtype.ext he : y = x) ▸ hy
  have hIS : I ≤ S := map_mono hAR
  have hI : I ≠ ⊥ := by
    intro he
    apply hescape
    intro x hx
    have hm : q (⟨x,hAL hx⟩ : L) ∈ I := mem_map_of_mem q hx
    have hh : q (⟨x,hAL hx⟩ : L) = 1 := mem_bot.mp (he ▸ hm)
    have hcore := (QuotientGroup.eq_one_iff (⟨x,hAL hx⟩ : L)).mp hh
    exact (localGroup_core_eq F d beta) ▸ mem_map_of_mem L.subtype hcore
  have hIΩ := source_rank_one_elementary_le_sylow_omega Mb S I hIS
  have hSI : (S : Subgroup (L ⧸ pCore 2 L)) ≤ normalizer (I : Set (L ⧸ pCore 2 L)) := by
    apply (show (S : Subgroup (L ⧸ pCore 2 L)) ≤ centralizer (I : Set (L ⧸ pCore 2 L)) from ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro s hs
    exact fun x hx => ((mem_omegaCenterIn_iff _ _).mp (hIΩ hx)).2.1 s hs |>.symm
  have hN : normalizer (S : Set (L ⧸ pCore 2 L)) ≤ normalizer (I : Set (L ⧸ pCore 2 L)) := by
    intro z hz
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
    have hgR : g ∈ normalizer (R : Set L) := by
      have he := quotientSylow_normalizer_comap R
      exact he ▸ hz
    have hgm : (g : G) • mid = mid := by
      have he := (source_edge_local_normalizer h d hbm Mb R hR).2
      have hh : g ∈ (stabilizer F mid).subgroupOf L := he.symm ▸ hgR
      exact hh
    have hgb : (g : G) • beta = beta := d.local_le beta g.property
    have ht := (source_edge_transitive_or_dihedral h hB d hbm.symm Mm).resolve_right hnd
    obtain ⟨Rmid,hRmid⟩ := source_edge_core_local_sylow h hB d hbm.symm
    have hga : (graph F).Adj mid ((g : G) • a') := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F (g : G)).map_adj_iff.mpr ham.symm
      change (graph F).Adj ((g : G) • mid) ((g : G) • a') at hh
      rwa [hgm] at hh
    have hgan : (g : G) • a' ≠ beta := by
      intro he
      exact hne ((MulAction.injective (g : G)) (hgb.trans he.symm))
    obtain ⟨s,hs,hsg⟩ := source_edge_sylow_transitive_of_edge_transitive h d hbm.symm Mm
      Rmid hRmid ht hga ham.symm hgan hne.symm
    have hsR : s ∈ (R : Subgroup L).map L.subtype := by
      rw [hR]
      simpa only [inf_comm] using hs
    obtain ⟨sL,hsL,rfl⟩ := hsR
    have hsN := hSI (mem_map_of_mem q hsL)
    have hsgN : q (sL*g) ∈ normalizer (I : Set (L ⧸ pCore 2 L)) := by
      apply le_normalizer_map q
      apply mem_map_of_mem q
      rw [←subgroupOf_normalizer_eq hAL]
      apply hn
      change ((sL : G)*(g : G)) • a' = a'
      rw [mul_smul]
      exact hsg
    have hh := (normalizer (I : Set (L ⧸ pCore 2 L))).mul_mem
      ((normalizer (I : Set (L ⧸ pCore 2 L))).inv_mem hsN) hsgN
    simpa only [map_mul,inv_mul_cancel_left] using hh
  refine ⟨R,?_⟩
  have he := source_rank_one_omega_generated Mb S I hIS hI
  exact le_antisymm hIΩ (he ▸ conjugateSpanBy_le le_rfl hN)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
