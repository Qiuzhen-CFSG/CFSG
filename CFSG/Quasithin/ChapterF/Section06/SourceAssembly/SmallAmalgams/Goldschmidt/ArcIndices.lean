module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ArcSingularity

/-!
# Stabilizer indices of regular cubic arcs

The orbit of a permitted next vertex under the literal pointwise arc fixer is
exactly the forward extension set. Orbit--stabilizer gives index two after a
nontrivial arc and index three after a vertex. These are the maximal-subgroup
steps in Goldschmidt (2.13), with the original coset action and subgroup maps.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.13), p.384.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem graphAction : GraphAction (RankTwo.graph F) G :=
  ⟨fun g _ _ h => (translationGraphIso F g).toHom.map_adj h⟩

theorem pathStabilizer_snoc {n : ℕ} {v z : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) n v) (hz : (RankTwo.graph F).Adj p.endpoint z) :
    RankTwo.pathStabilizer F (p.snoc hz) =
      RankTwo.pathStabilizer F p ⊓ RankTwo.stabilizer F z := by
  ext a
  change (∀ y ∈ (p.snoc hz).vertices, a • y = y) ↔
    (∀ y ∈ p.vertices, a • y = y) ∧ a • z = z
  simp only [BasedWalk.vertices_snoc, List.mem_append, List.mem_singleton]
  aesop

theorem pathStabilizer_forward_orbit {n : ℕ} {v z : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) n v) (hp : RightRegular (A := G) p)
    (hz : Theory.GroupAction.CubicTree.Forward p z) :
    MulAction.orbit (RankTwo.pathStabilizer F p) z =
      {w | Theory.GroupAction.CubicTree.Forward p w} := by
  ext w
  constructor
  · rintro ⟨a, rfl⟩
    exact forward_smul_of_fixes graphAction p a a.property hz
  · intro hw
    obtain ⟨a, ha, haw⟩ := hp z w hz hw
    exact ⟨⟨a, ha⟩, haw⟩

theorem pathStabilizer_snoc_relIndex {n : ℕ} {v z : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) n v) (hp : RightRegular (A := G) p)
    (hz : Theory.GroupAction.CubicTree.Forward p z) :
    (RankTwo.pathStabilizer F (p.snoc (forward_adj p hz))).relIndex
      (RankTwo.pathStabilizer F p) =
        Nat.card {w | Theory.GroupAction.CubicTree.Forward p w} := by
  have he : (RankTwo.pathStabilizer F (p.snoc (forward_adj p hz))).subgroupOf
      (RankTwo.pathStabilizer F p) =
      MulAction.stabilizer (RankTwo.pathStabilizer F p) z := by
    ext a
    rw [pathStabilizer_snoc]
    change ((a : G) ∈ RankTwo.pathStabilizer F p ∧ (a : G) • z = z) ↔
      (a : G) • z = z
    exact and_iff_right a.property
  rw [Subgroup.relIndex, he, MulAction.index_stabilizer,
    pathStabilizer_forward_orbit p hp hz, Nat.card_coe_set_eq]

theorem CubicTreeAction.pathStabilizer_snoc_index_two (h : CubicTreeAction F)
    {n : ℕ} {v z : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) (n + 1) v)
    (hp : RightRegular (A := G) p) (hz : Theory.GroupAction.CubicTree.Forward p z) :
    (RankTwo.pathStabilizer F (p.snoc (forward_adj p hz))).relIndex
      (RankTwo.pathStabilizer F p) = 2 := by
  rw [pathStabilizer_snoc_relIndex p hp hz]
  exact card_forward_of_cubic p (h.card_neighbor p.endpoint)

theorem CubicTreeAction.pathStabilizer_edge_index_three (h : CubicTreeAction F)
    {v z : RankTwo.Vertex F} (hz : (RankTwo.graph F).Adj v z) :
    (RankTwo.pathStabilizer F (show BasedWalk (RankTwo.graph F) 1 v from
      ⟨⟨z, hz⟩, PUnit.unit⟩)).relIndex (RankTwo.stabilizer F v) = 3 := by
  let p : BasedWalk (RankTwo.graph F) 0 v := PUnit.unit
  have he : RankTwo.pathStabilizer F p = RankTwo.stabilizer F v := by
    ext a
    change (∀ y ∈ [v], a • y = y) ↔ a • v = v
    simp
  have hi := pathStabilizer_snoc_relIndex p (h.zero_arc_regular v) hz
  rw [he] at hi
  exact hi.trans (h.card_neighbor v)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
