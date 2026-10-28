module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralCoreIndex
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LargeLocalQuotients

/-!
# Two-cores and the two neighboring edge stabilizers

The local symmetric-three quotient gives index two for the vertex two-core
in each incident edge. Short-arc regularity gives the same index for the
intersection of two distinct incident edge stabilizers, proving equality.
The literal core image is normalized by the vertex stabilizer.

Source: the local-action step in Goldschmidt (6.4), printed p.397.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem CubicTreeAction.vertexTwoCore_edge_relIndex (h : CubicTreeAction F)
    {a b : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b)
    (e : ((RankTwo.stabilizer F b) ⧸ pCore 2 (RankTwo.stabilizer F b)) ≃*
      Equiv.Perm (Fin 3)) :
    ((pCore 2 (RankTwo.stabilizer F b)).map (RankTwo.stabilizer F b).subtype).relIndex
      (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b) = 2 := by
  let H := RankTwo.stabilizer F b
  let P := (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b).subgroupOf H
  have hi : P.index = 3 := h.edge_vertex_relIndex hab
  have hQP : pCore 2 H ≤ P := by
    intro x hx
    exact h.vertexTwoCore_le_edge hab ⟨x, hx, rfl⟩
  have ht := Subgroup.relIndex_mul_index hQP
  rw [hi, SymmetricThreeTwoCore.core_index e] at ht
  have htwo : (pCore 2 H).relIndex P = 2 := by omega
  have hmap : P.map H.subtype = RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_right
  rw [← Subgroup.relIndex_map_map_of_injective (pCore 2 H) P H.subtype_injective,
    hmap] at htwo
  exact htwo

theorem CubicTreeAction.vertexTwoCore_eq_twoEdges (h : CubicTreeAction F)
    {s : ℕ} (hs : 2 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) (a : ℤ)
    (e : ((RankTwo.stabilizer F (t.vertex (a + 1))) ⧸
      pCore 2 (RankTwo.stabilizer F (t.vertex (a + 1)))) ≃* Equiv.Perm (Fin 3)) :
    (pCore 2 (RankTwo.stabilizer F (t.vertex (a + 1)))).map
      (RankTwo.stabilizer F (t.vertex (a + 1))).subtype =
      t.edgeStabilizer a ⊓ t.edgeStabilizer (a + 1) := by
  let H := RankTwo.stabilizer F (t.vertex (a + 1))
  let Q := (pCore 2 H).map H.subtype
  let K := t.edgeStabilizer a ⊓ t.edgeStabilizer (a + 1)
  have hQa : Q ≤ t.edgeStabilizer a := h.vertexTwoCore_le_edge (t.adjacent a)
  have hQb : Q ≤ t.edgeStabilizer (a + 1) := by
    have hh := h.vertexTwoCore_le_edge (t.adjacent (a + 1)).symm
    exact hh.trans (by rw [inf_comm]; rfl)
  have hQK : Q ≤ K := le_inf hQa hQb
  let p : BasedWalk (RankTwo.graph F) 1 (t.vertex a) :=
    ⟨⟨t.vertex (a + 1), t.adjacent a⟩, PUnit.unit⟩
  have hf : Theory.GroupAction.CubicTree.Forward p (t.vertex (a + 1 + 1)) := by
    refine ⟨t.adjacent (a + 1), ?_⟩
    intro he
    have hh := t.injective he
    omega
  have hi := h.pathStabilizer_snoc_index_two p (hshort 1 _ p (by omega) trivial) hf
  have he : RankTwo.pathStabilizer F p = t.edgeStabilizer a := by
    ext g
    change (∀ y ∈ [t.vertex a, t.vertex (a + 1)], g • y = y) ↔
      g • t.vertex a = t.vertex a ∧ g • t.vertex (a + 1) = t.vertex (a + 1)
    simp
  have heK : t.edgeStabilizer a ⊓ RankTwo.stabilizer F (t.vertex (a + 1 + 1)) = K := by
    ext g
    change ((_ ∧ _) ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _))
    aesop
  rw [pathStabilizer_snoc, he, heK] at hi
  have hQidx : Q.relIndex (t.edgeStabilizer a) = 2 :=
    h.vertexTwoCore_edge_relIndex (t.adjacent a) e
  have ht := Subgroup.relIndex_mul_relIndex Q K (t.edgeStabilizer a) hQK inf_le_left
  rw [hi, hQidx] at ht
  have hrel : Q.relIndex K = 1 := by omega
  exact le_antisymm hQK (Subgroup.relIndex_eq_one.mp hrel)

theorem vertexStabilizer_le_normalizer_twoCoreImage (v : RankTwo.Vertex F) :
    RankTwo.stabilizer F v ≤ normalizer
      (((pCore 2 (RankTwo.stabilizer F v)).map (RankTwo.stabilizer F v).subtype) : Set G) := by
  let H := RankTwo.stabilizer F v
  let Q := (pCore 2 H).map H.subtype
  have he : Q.subgroupOf H = pCore 2 H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective (pCore 2 H)
  let : (Q.subgroupOf H).Normal := he ▸ inferInstance
  exact Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.map_subtype_le (pCore 2 H))

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
