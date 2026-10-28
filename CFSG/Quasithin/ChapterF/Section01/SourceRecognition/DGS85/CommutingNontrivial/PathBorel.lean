module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FullCoreProduct
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborSylow

/-!
# The Borel image of a two-edge path stabilizer

When the middle local quotient is not dihedral of order ten, its edge
Sylow acts transitively on the other neighbors. An edge element at beta
can therefore be corrected by this Sylow to fix the other path endpoint.
The middle core already fixes both endpoints and fills the beta quotient
Sylow, so the correction does not shrink the image: the path stabilizer
maps onto the whole beta Borel.

This supplies the literal path actor used on the natural residual section
in DGS, *Groups and Graphs* (1985), 8.5, printed p.139. The middle D₁₀
exception remains an explicit hypothesis; no two-transitivity is asserted
for that model.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem path_borel_image_of_correction
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {beta mid a' : Vertex (family P)}
    (hbm : (graph (family P)).Adj beta mid)
    (ham : (graph (family P)).Adj a' mid)
    (hescape : ¬ Q (family P) mid ≤ Q (family P) beta)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,k))
    (hcorr : ∀ g ∈ graphLocalGroup (family P) beta ⊓ stabilizer (family P) mid,
      ∃ s ∈ (stabilizer (family P) beta ⊓ stabilizer (family P) mid).pCoreIn 2,
        (s*g) • a' = a') :
    let F := family P
    let L := graphLocalGroup F beta
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    ∃ T : Sylow 2 SL(2,k), ((Q F mid).subgroupOf L).map q = T ∧
      ((stabilizer F mid ⊓ stabilizer F a').subgroupOf L).map q = normalizer (T : Set SL(2,k)) ∧
      ∀ l : L, q l ∈ normalizer (T : Set SL(2,k)) ↔ (l : G) • mid = mid := by
  let := finite_endpoints h
  let F := family P
  let L := graphLocalGroup F beta
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let E := stabilizer F beta ⊓ stabilizer F mid
  let H := (stabilizer F mid ⊓ stabilizer F a').subgroupOf L
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨T,hT,hTf⟩ := linear_neighbor_core_sylow_image h hB hS hbm hescape e
  have hTL : (T : Subgroup SL(2,k)) ≤ H.map q := by
    rw [←hT]
    apply map_mono
    exact comap_mono (le_inf (Q_le_stabilizer F mid)
      ((source_Z_Q_U h mid).2.trans ((ballKernel_one_le_edge F ham.symm).trans inf_le_right)))
  obtain ⟨R,hR⟩ := source_edge_vertex_sylow h hS hbm
  have hReq := sylow_image_eq_edge_core (stabilizer F beta) E inf_le_left
    (source_edge_core_sylow h hB hbm) R hR
  have hEL : E.pCoreIn 2 ≤ L := hReq ▸ sylow_le_sylowGenerated _ R
  have hEN : ((E.pCoreIn 2).subgroupOf L).map q ≤ normalizer (T : Set SL(2,k)) := by
    rintro _ ⟨x,hx,rfl⟩
    exact (hTf x).mpr ((pCoreIn_le 2 E hx).2)
  have hET : ((E.pCoreIn 2).subgroupOf L).map q ≤ T := by
    change ((pCoreIn 2 E).comap L.subtype).map q ≤ T
    have hp := ((isPGroup_pCoreIn 2 E).comap_subtype (K := L)).map q
    have hh := hp.inf_normalizer_sylow T
    rw [inf_eq_left.mpr (by simpa only [Subgroup.subgroupOf] using hEN)] at hh
    exact inf_eq_left.mp hh.symm
  refine ⟨T,hT,le_antisymm ?_ ?_,hTf⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact (hTf x).mpr hx.1
  · intro z hz
    obtain ⟨g,rfl⟩ := hq z
    obtain ⟨s,hs,hsg⟩ := hcorr g ⟨g.property,(hTf g).mp hz⟩
    let sL : L := ⟨s,hEL hs⟩
    have hsi : q sL ∈ H.map q := hTL (hET (mem_map_of_mem q hs))
    have hsgi : q (sL*g) ∈ H.map q := mem_map_of_mem q (show sL*g ∈ H from
      ⟨by change (s*(g : G)) • mid = mid
          rw [mul_smul,(hTf g).mp hz]
          exact (pCoreIn_le 2 E hs).2,hsg⟩)
    have hi := (H.map q).mul_mem ((H.map q).inv_mem hsi) hsgi
    simpa only [map_mul,inv_mul_cancel_left] using hi

private theorem edge_correction_of_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {beta mid a' : Vertex (family P)}
    (hbm : (graph (family P)).Adj beta mid)
    (ham : (graph (family P)).Adj a' mid) (hne : beta ≠ a')
    (M : IsRankOneModel (d.localGroup mid ⧸ pCore 2 (d.localGroup mid)))
    (ht : ∀ x y : Vertex (family P), (graph (family P)).Adj mid x →
      (graph (family P)).Adj mid y → x ≠ beta → y ≠ beta →
      ∃ g ∈ d.localGroup mid ⊓ stabilizer (family P) beta, g • x = y)
    (g : G) (hg : g ∈ stabilizer (family P) beta ⊓ stabilizer (family P) mid) :
    ∃ s ∈ (stabilizer (family P) beta ⊓ stabilizer (family P) mid).pCoreIn 2,
      (s*g) • a' = a' := by
  let := finite_endpoints h
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hbm.symm
  have hga : (graph (family P)).Adj mid (g • a') := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr ham.symm
    change (graph (family P)).Adj (g • mid) (g • a') at hh
    rwa [show g • mid = mid from hg.2] at hh
  have hgan : g • a' ≠ beta := by
    intro he
    exact hne ((MulAction.injective g) (hg.1.trans he.symm))
  obtain ⟨s,hs,he⟩ := source_edge_sylow_transitive_of_edge_transitive h d hbm.symm M R hR ht
    hga ham.symm hgan hne.symm
  refine ⟨s,?_,?_⟩
  · simpa only [inf_comm] using hs
  · simpa only [mul_smul] using he
/-- The original path stabilizer fills the beta Borel when the middle
local model is not D₁₀. The same Sylow is the image of the middle core. -/
theorem source_linear_path_borel_image_of_not_dihedral
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {beta mid a' : Vertex (family P)}
    (hbm : (graph (family P)).Adj beta mid)
    (ham : (graph (family P)).Adj a' mid) (hne : beta ≠ a')
    (hescape : ¬ Q (family P) mid ≤ Q (family P) beta)
    (M : IsRankOneModel (d.localGroup mid ⧸ pCore 2 (d.localGroup mid)))
    (hnd : ¬ Nonempty ((d.localGroup mid ⧸ pCore 2 (d.localGroup mid)) ≃*
      DihedralGroup 5))
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃*
      SL(2,k)) :
    let F := family P
    let L := graphLocalGroup F beta
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    ∃ T : Sylow 2 SL(2,k), ((Q F mid).subgroupOf L).map q = T ∧
      ((stabilizer F mid ⊓ stabilizer F a').subgroupOf L).map q =
        normalizer (T : Set SL(2,k)) ∧
      ∀ l : L, q l ∈ normalizer (T : Set SL(2,k)) ↔ (l : G) • mid = mid := by
  have ht := (source_edge_transitive_or_dihedral h hB d hbm.symm M).resolve_right hnd
  apply path_borel_image_of_correction h hB hS hbm ham hescape e
  intro g hg
  exact edge_correction_of_transitive h hB d hbm ham hne M ht g
    ⟨sylowGenerated_le _ hg.1,hg.2⟩

/-- The same path-Borel statement on the literal reduced F1.11 graph. The
6.5 normalizer obstruction supplies the required escaping-core hypothesis;
the path vertices and their local model hypotheses remain the actual source
data at the chosen critical configuration. -/
theorem reduced_linear_path_borel_image_of_not_dihedral
    {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓
          Q (Reduction.reducedFamily J S₀) v : Subgroup (Reduction.G₀ J S₀)) :
          Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {beta mid a' : Vertex (Reduction.reducedFamily J S₀)}
    (hbm : (graph (Reduction.reducedFamily J S₀)).Adj beta mid)
    (ham : (graph (Reduction.reducedFamily J S₀)).Adj a' mid)
    (hne : beta ≠ a')
    (hnd : ¬ Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) mid ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) mid)) ≃*
      DihedralGroup 5))
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) beta)) ≃* SL(2,k)) :
    let F := Reduction.reducedFamily J S₀
    let L := graphLocalGroup F beta
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    ∃ T : Sylow 2 SL(2,k), ((Q F mid).subgroupOf L).map q = T ∧
      ((stabilizer F mid ⊓ stabilizer F a').subgroupOf L).map q =
        normalizer (T : Set SL(2,k)) ∧
      ∀ l : L, q l ∈ normalizer (T : Set SL(2,k)) ↔ (l : Reduction.G₀ J S₀) • mid = mid := by
  let F := Reduction.reducedFamily J S₀
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  have hescape : ¬ Q F mid ≤ Q F beta := by
    exact core_escape_of_intersection_obstruction
      (F₀ := F) (v := beta) (w := mid) (hob mid beta hbm.symm)
  exact source_linear_path_borel_image_of_not_dihedral ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    d hbm ham hne hescape (models mid) hnd e

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
