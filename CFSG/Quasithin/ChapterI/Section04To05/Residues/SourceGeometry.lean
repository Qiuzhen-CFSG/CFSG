module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.Digon

/-!
# Connectivity, flags and exact residue kernels from D1–D4

The three pairs of parabolics generate their vertex groups by D3, while
the vertices generate the whole group by D4. The actual coset incidence
graph and every vertex residue are therefore connected. The middle product
proved from D2–D3 yields flag transitivity and identifies the induced residue
with the intrinsic local coset geometry. Its kernel is the original local
two-core; the action on the full geometry is faithful by D4.

Source: Aschbacher–Smith I.5.3 and I.5.4(3–4), printed pp.419–420. No point
faithfulness, finite global geometry, or recognition conclusion is assumed.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G K : Type*} [Group G] [Group K] {D : Diagram} (S : DSystem D G)

theorem local_residue_generate (i : Fin 3) :
    (⨆ j : {j : Fin 3 // j ≠ i}, (S.family j.val).subgroupOf (S.family i)) = ⊤ := by
  apply top_unique
  fin_cases i
  · rw [← S.point_parabolics_generate]
    exact sup_le (le_iSup (fun j : {j : Fin 3 // j ≠ 0} =>
      (S.family j.val).subgroupOf (S.family 0)) ⟨1, by decide⟩)
      (le_iSup (fun j : {j : Fin 3 // j ≠ 0} =>
        (S.family j.val).subgroupOf (S.family 0)) ⟨2, by decide⟩)
  · rw [← S.line_parabolics_generate]
    exact sup_le (le_iSup (fun j : {j : Fin 3 // j ≠ 1} =>
      (S.family j.val).subgroupOf (S.family 1)) ⟨0, by decide⟩)
      (le_iSup (fun j : {j : Fin 3 // j ≠ 1} =>
        (S.family j.val).subgroupOf (S.family 1)) ⟨2, by decide⟩)
  · rw [← S.plane_parabolics_generate]
    exact sup_le (le_iSup (fun j : {j : Fin 3 // j ≠ 2} =>
      (S.family j.val).subgroupOf (S.family 2)) ⟨0, by decide⟩)
      (le_iSup (fun j : {j : Fin 3 // j ≠ 2} =>
        (S.family j.val).subgroupOf (S.family 2)) ⟨1, by decide⟩)

theorem incidenceGraph_connected : S.incidenceGraph.Connected :=
  CosetGeometry.incidenceGraph_connected S.family S.generate

theorem residueGraph_connected (v : S.Vertex) :
    (CosetGeometry.residueGraph S.family v).Connected :=
  CosetGeometry.residueGraph_connected S.family S.local_residue_generate v

theorem flags_transitive {s t : Set S.Vertex} (hs : S.IsFlag s) (ht : S.IsFlag t)
    (htypes : CosetGeometry.Vertex.type '' s = CosetGeometry.Vertex.type '' t) :
    ∃ g : G, (fun v : S.Vertex => g • v) '' s = t :=
  CosetGeometry.flag_transitive S.family S.middleProduct hs ht htypes

theorem flag_common_representative {s : Set S.Vertex} (hs : S.IsFlag s) :
    ∃ g : G, ∀ v ∈ s, (g : G ⧸ S.family v.type) = v.coset :=
  hs.common_representative S.family S.middleProduct

/-- I.5.3(3), with the graph of the original induced residue. -/
def intrinsicResidueGraphIso (i : Fin 3) :
    CosetGeometry.incidenceGraph (CosetGeometry.intrinsicFamily S.family i) ≃g
      CosetGeometry.residueGraph S.family (S.baseVertex i) :=
  CosetGeometry.residueIntrinsicGraphIso S.family i S.middleProduct

/-- I.5.4(3), with the original intrinsic vertex-group action. -/
theorem residue_kernel (i : Fin 3) :
    (MulAction.toPermHom (S.family i) (S.Residue (S.baseVertex i))).ker =
      pCore 2 (S.family i) := by
  rw [CosetGeometry.residue_action_kernel_chamber]
  exact S.local_normalCore i

/-- The actual model quotient of the induced residue, preserving all incidence. -/
def modelResidueGraphIso (i : Fin 3)
    (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K) :
    CosetGeometry.residueGraph S.family (S.baseVertex i) ≃g
      CosetGeometry.incidenceGraph
        (fun j => (CosetGeometry.intrinsicPair S.family i j).map
          (S.localQuotientMap i e)) :=
  CosetGeometry.residueTransportGraphIso S.family i (S.localQuotientMap i e)
    (S.localQuotientMap_surjective i e) (S.localQuotientMap_ker_le_intrinsic i e)
    S.middleProduct

theorem model_residue_kernel (i : Fin 3)
    (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K) :
    (MulAction.toPermHom K (CosetGeometry.Vertex
      (fun j => (CosetGeometry.intrinsicPair S.family i j).map
        (S.localQuotientMap i e)))).ker = ⊥ := by
  rw [← CosetGeometry.residueTransport_action_kernel_map S.family i
    (S.localQuotientMap i e) (S.localQuotientMap_surjective i e)
    (S.localQuotientMap_ker_le_intrinsic i e), S.residue_kernel,
    ← S.localQuotientMap_ker i e]
  exact (Subgroup.map_eq_bot_iff _).mpr le_rfl

end Quasithin.I5.DSystem
