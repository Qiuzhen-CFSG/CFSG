module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FullCoreProduct
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NeighborActions
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.RootedExtensions

/-!
# Three-edge paths from the full adjacent-core product

If one edge two-core is the product of its vertex cores, the same holds at
every edge. In a non-dihedral rank-one local action, the preceding vertex
core is transitive on forward neighbors. It fixes the preceding two-edge
path, which proves three-walk transitivity at every vertex.

The small-solvable / A₅ consumer uses this after excluding the dihedral
quotient, for the actual A₅/Sz(2) actors. This is the short-path argument
needed by the source remote-layer proof, not a four-walk hypothesis.
Source: DGS, *Groups and Graphs* (1985), (3.4), (11.4)--(11.6),
pp.74,171--173.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem core_fix_adjacent (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {g : G} (hg : g ∈ Q (family P) v) : g • w = w :=
  ((source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge (family P) hvw).trans inf_le_right)) hg

private theorem short_right_regular_of_core_forward
    (h : LocallyRankOneTriple P B)
    (ht : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ∀ x y : Vertex (family P), (graph (family P)).Adj v x →
        (graph (family P)).Adj v y → x ≠ w → y ≠ w →
        ∃ g ∈ Q (family P) w, g • x = y)
    {u : Vertex (family P)} (p : BasedWalk (graph (family P)) 2 u) :
    RightRegular (A := G) p := by
  intro x y hx hy
  let v : Vertex (family P) := p.1
  let w : Vertex (family P) := p.2.1
  have huv : (graph (family P)).Adj u v := p.1.property
  have hvw : (graph (family P)).Adj v w := p.2.1.property
  change (graph (family P)).Adj w x ∧ x ≠ v at hx
  change (graph (family P)).Adj w y ∧ y ≠ v at hy
  obtain ⟨g,hg,he⟩ := ht w v hvw.symm x y hx.1 hy.1 hx.2 hy.2
  refine ⟨g,?_,he⟩
  change ∀ z ∈ [u,v,w], g • z = z
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨core_fix_adjacent h huv.symm hg,Q_le_stabilizer _ v hg,
    core_fix_adjacent h hvw hg⟩

private theorem one_walk_transitive (u : Vertex (family P)) :
    RootPathTransitive (graph (family P)) G u 1 := by
  intro p q _ _
  obtain ⟨g,hg,he⟩ := locally_transitive (family P) p.1.property q.1.property
  refine ⟨g,hg,?_⟩
  change [u,(p.1 : Vertex (family P))].map (g • ·) = [u,(q.1 : Vertex (family P))]
  simp only [List.map_cons,List.map_nil,show g • u = u from hg,he]

private theorem three_walk_of_core_forward
    (h : LocallyRankOneTriple P B)
    (ht : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ∀ x y : Vertex (family P), (graph (family P)).Adj v x →
        (graph (family P)).Adj v y → x ≠ w → y ≠ w →
        ∃ g ∈ Q (family P) w, g • x = y)
    (u : Vertex (family P)) : RootPathTransitive (graph (family P)) G u 3 := by
  have hact : GraphAction (graph (family P)) G :=
    ⟨fun g _ _ he => (Subgroup.CosetGeometry.translationGraphIso (family P) g).toHom.map_adj he⟩
  have htwo : RootPathTransitive (graph (family P)) G u 2 := by
    apply (one_walk_transitive u).succ_of_rightRegular hact
    intro p _ x y hx hy
    let v : Vertex (family P) := p.1
    have huv : (graph (family P)).Adj u v := p.1.property
    change (graph (family P)).Adj v x ∧ x ≠ u at hx
    change (graph (family P)).Adj v y ∧ y ≠ u at hy
    obtain ⟨g,hg,he⟩ := ht v u huv.symm x y hx.1 hy.1 hx.2 hy.2
    refine ⟨g,?_,he⟩
    change ∀ z ∈ [u,v], g • z = z
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    exact ⟨Q_le_stabilizer _ u hg,core_fix_adjacent h huv hg⟩
  exact htwo.succ_of_rightRegular hact (fun p _ => short_right_regular_of_core_forward h ht p)

/-- The source full-core product and the actual non-dihedral local catalogue
give three-walk transitivity everywhere, without a path-action premise. -/
theorem source_three_walk_transitive_of_full_core_product
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hprod : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      Q (family P) a ⊔ Q (family P) b)
    (models : ∀ v : Vertex (family P),
      IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hnot : ∀ v : Vertex (family P),
      ¬ Nonempty ((d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* DihedralGroup 5))
    (u : Vertex (family P)) : RootPathTransitive (graph (family P)) G u 3 := by
  apply three_walk_of_core_forward h ?_ u
  intro v w hvw x y hx hy hxw hyw
  have haction := (source_edge_transitive_or_dihedral h hB d hvw (models v)).resolve_right (hnot v)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hvw
  exact source_full_product_core_transitive h d hvw (models v) R hR
    (source_full_core_product_all_edges (family P) hab hprod.symm hvw)
    haction hx hy hxw hyw

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
