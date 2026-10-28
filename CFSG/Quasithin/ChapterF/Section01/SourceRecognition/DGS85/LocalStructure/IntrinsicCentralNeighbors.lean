module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicEdgeGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NaturalEscape

/-!
# Central neighboring centers without enlarged quotient models

The intrinsic two-edge generation theorem puts the intersection of the
edge omega-centers in the middle local omega-center. The existing source
centrality theorem makes that omega-center trivial. The original center
spans are the actual edge omega-centers, so they are disjoint. This
removes the enlarged-model premise from the central-neighbor disjointness
calculation used in DGS 8.6 and the subsequent conjugate-subgroup argument.

The final application obtains centrality from the already proved commuting
critical geometry; its only hypotheses are original F.1.1, criticality,
commutation and the indicated path position. A separate application maps
the result into the original group and retains the same conjugating
element, full Borel and reduced-to-original inclusion. No finiteness of
the completion or tree hypothesis is used.

The unrestricted order-144 enlargement and the other Chapter 8/model and
source-assembly premises remain outstanding. This proves the indicated
central-neighbor consequence, not all of 6.1 or Chapter 8.
Source: DGS, *Groups and Graphs* (1985), 8.1 and 8.6, pp.132--133,139;
the original reduction is on pp.95--96.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))

/-- Distinct neighbors in a central orbit have disjoint original center spans. -/
theorem reduced_intrinsic_central_neighbor_centers_disjoint (h : HypothesisF11 L S)
    {v w z : Vertex F} (hw : (graph F).Adj v w) (hz : (graph F).Adj v z)
    (hne : w ≠ z) (hcentral : Z F w = omegaCenterIn (graphLocalGroup F w)) :
    Disjoint (Z F w) (Z F z) := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let d := reducedFullEarlierLocalTheorems h
  obtain ⟨g,hg,hgz⟩ := locally_transitive F hw hz
  have hcentralz : Z F z = omegaCenterIn (graphLocalGroup F z) := by
    rw [←hgz,Z_translate,graphLocalGroup_conjugate ht,
      ←NilesRankOneKernel.omegaCenterIn_map_injective
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,hcentral]
  have hs := (source_central_edge_seed ht (reduced_borel_core_sylow h) d hw hcentral).1
  have ht' := (source_central_edge_seed ht (reduced_borel_core_sylow h) d hz hcentralz).1
  have hc : omegaCenterIn (graphLocalGroup F v) = ⊥ :=
    local_omega_eq_bot_of_neighbor_central ht d hw hcentral
  have hi := graph_intrinsic_edge_omega_inter_le ht (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hw hz hne
  rw [hs,ht',hc] at hi
  exact disjoint_iff.mpr (bot_unique hi)

/-- Literal conjugation of every subgroup of the central neighbor span is disjoint
when the element fixes the middle vertex but moves that neighbor. -/
theorem reduced_intrinsic_central_subgroup_disjoint_conjugate (h : HypothesisF11 L S)
    {v w : Vertex F} (hw : (graph F).Adj v w)
    (hcentral : Z F w = omegaCenterIn (graphLocalGroup F w))
    (H : Subgroup (G₀ L S)) (hH : H ≤ Z F w)
    (g : G₀ L S) (hgv : g ∈ stabilizer F v) (hgw : g ∉ stabilizer F w) :
    Disjoint H (H.map (MulAut.conj g).toMonoidHom) := by
  let := finite_endpoints (reduced_triple h)
  have hz : (graph F).Adj v (g • w) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hw
    change (graph F).Adj (g • v) (g • w) at hh
    rwa [show g • v = v from hgv] at hh
  have hn : w ≠ g • w := fun he => hgw he.symm
  have hd := reduced_intrinsic_central_neighbor_centers_disjoint h hw hz hn hcentral
  rw [Z_translate] at hd
  exact hd.mono hH (map_mono hH)

/-- The original F.1.1 inclusion preserves this disjointness and the literal
conjugating element; the full original Borel has not been replaced. -/
theorem original_intrinsic_central_subgroup_disjoint_conjugate (h : HypothesisF11 L S)
    {v w : Vertex F} (hw : (graph F).Adj v w)
    (hcentral : Z F w = omegaCenterIn (graphLocalGroup F w))
    (H : Subgroup (G₀ L S)) (hH : H ≤ Z F w)
    (g : G₀ L S) (hgv : g ∈ stabilizer F v) (hgw : g ∉ stabilizer F w) :
    Disjoint (H.map (G₀ L S).subtype)
      ((H.map (G₀ L S).subtype).map (MulAut.conj (g : G)).toMonoidHom) := by
  have hd := reduced_intrinsic_central_subgroup_disjoint_conjugate h hw hcentral H hH g hgv hgw
  apply disjoint_iff.mpr
  have hm := congrArg (Subgroup.map (G₀ L S).subtype) (disjoint_iff.mp hd)
  rw [Subgroup.map_inf _ _ _ (G₀ L S).subtype_injective,Subgroup.map_bot] at hm
  have he : (H.map (MulAut.conj g).toMonoidHom).map (G₀ L S).subtype =
      (H.map (G₀ L S).subtype).map (MulAut.conj (g : G)).toMonoidHom := by
    rw [Subgroup.map_map,Subgroup.map_map]
    rfl
  rw [he] at hm
  exact hm

/-- Actual Chapter 8 critical geometry supplies the centrality hypothesis.
The source 8.6 central-neighbor disjointness now has no actor-model premise. -/
theorem reduced_commuting_critical_neighbor_centers_disjoint (h : HypothesisF11 L S)
    {a beta a' z : Vertex F} (hc : IsCriticalPair F a a')
    (hab : (graph F).Adj a beta)
    (hd : (graph F).dist beta a' + 1 = b F)
    (hb : 1 < b F) (hcomm : ⁅Z F a,Z F a'⁆ = ⊥)
    (haz : (graph F).Adj a z) (hne : beta ≠ z) :
    Disjoint (Z F beta) (Z F z) := by
  have hcentral := (source_critical_geometry (reduced_triple h)
    (reducedFullEarlierLocalTheorems h) hc hab hd hb hcomm).2.2.1
  exact reduced_intrinsic_central_neighbor_centers_disjoint h hab haz hne hcentral

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
