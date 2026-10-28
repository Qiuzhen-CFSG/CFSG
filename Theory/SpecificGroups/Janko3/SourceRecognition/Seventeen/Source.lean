module
public import Theory.PGroupCore
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Graph

/-!
# The literal hypotheses of Baumeister Lemma 2.7

`SourceData` records all three subgroup types, all three actual pairwise
intersections, generation, and the self-centralizing two-core of H₁.
The split point group is an actual semidirect product on a binary four-space;
its action is retained rather than replaced by an unrelated family tag.

The point and pair orders give index two on H₁ ∩ H₂. An outside involution
in H₂ therefore gives the connected graph from `Graph`. The remaining
geometric implications are applied to this same marked configuration.
Their explicit edge-stabilizer, local-transitivity and cubic-word inputs
are intermediate obligations, not additional hypotheses of the source
lemma. Embedding uniqueness and PSL₂(16):2 recognition are not asserted here.

Source: Baumeister, *A geometry for groups of J₃-type* (2007),
Lemma 2.7, printed p.497.
-/

@[expose] public section
open Subgroup MulAction
namespace Sporadic.Janko3.SourceRecognition.Seventeen

abbrev Plane := Multiplicative (Fin 4 → ZMod 2)
abbrev Complement := Multiplicative (ZMod 3) × DihedralGroup 5
abbrev PairGroup := Equiv.Perm (Fin 3) × DihedralGroup 5
abbrev TriangleGroup := alternatingGroup (Fin 5) × Multiplicative (ZMod 2)

/-- Baumeister 2.7(i–iii), with actual model isomorphisms. -/
structure SourceData (G : Type*) [Group G] where
  H1 : Subgroup G
  H2 : Subgroup G
  H3 : Subgroup G
  generated : H1 ⊔ H2 = ⊤
  action : Complement →* MulAut Plane
  pointEquiv : H1 ≃* Plane ⋊[action] Complement
  core_centralizer : centralizer (pCore 2 H1 : Set H1) = pCore 2 H1
  pairEquiv : H2 ≃* PairGroup
  triangleEquiv : H3 ≃* TriangleGroup
  overlap12 : (H1 ⊓ H2 : Subgroup G) ≃* Complement
  overlap13 : (H1 ⊓ H3 : Subgroup G) ≃*
    (alternatingGroup (Fin 4) × Multiplicative (ZMod 2))
  overlap23 : (H2 ⊓ H3 : Subgroup G) ≃*
    (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))

namespace SourceData
variable {G : Type*} [Group G] (S : SourceData G)

theorem point_card : Nat.card S.H1 = 480 := by
  rw [Nat.card_congr S.pointEquiv.toEquiv, SemidirectProduct.card]
  norm_num [Plane, Complement, Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, DihedralGroup.card]

theorem pair_card : Nat.card S.H2 = 60 := by
  rw [Nat.card_congr S.pairEquiv.toEquiv]
  norm_num [PairGroup, Nat.card_prod, Nat.card_eq_fintype_card, DihedralGroup.card,
    Fintype.card_perm, Nat.factorial]

theorem overlap_card : Nat.card (S.H1 ⊓ S.H2 : Subgroup G) = 30 := by
  rw [Nat.card_congr S.overlap12.toEquiv]
  norm_num [Complement, Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, DihedralGroup.card]

theorem overlap_index_two : (S.H1.subgroupOf S.H2).index = 2 := by
  have hc : Nat.card (S.H1.subgroupOf S.H2) = 30 := by
    rw [← inf_subgroupOf_right, Nat.card_congr (subgroupOfEquivOfLe
      (show S.H1 ⊓ S.H2 ≤ S.H2 from inf_le_right)).toEquiv]
    exact overlap_card S
  have h := (S.H1.subgroupOf S.H2).card_mul_index
  rw [hc, pair_card S] at h
  omega

abbrev cosetData (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1) : CosetGraph.Data G where
  point := S.H1
  swap := b
  square := hb
  outside := hbout

theorem connected (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1) (hb2 : b ∈ S.H2) :
    (CosetGraph.graph (cosetData S b hb hbout)).Connected := by
  let D := cosetData S b hb hbout
  exact CosetGraph.connected D (CosetGraph.generation_of_index_two D S.H2 hb2
    (overlap_index_two S) S.generated)

theorem geometric_consequences
    (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1) (hb2 : b ∈ S.H2)
    (hedge : CosetGraph.edgeStabilizer (cosetData S b hb hbout) = S.H2.subgroupOf S.H1)
    (htwo : CosetGraph.NeighborTwoTransitive (cosetData S b hb hbout))
    (h : G) (hh : h ∈ S.H1) (hcube : (b * h)^3 ∈ S.H1) :
    let D := cosetData S b hb hbout
    (CosetGraph.graph D).Connected ∧ CosetGraph.graph D = ⊤ ∧
      (∀ x : CosetGraph.Vertex D, Nat.card ((CosetGraph.graph D).neighborSet x) = 16) ∧
      Nat.card (CosetGraph.Vertex D) = 17 ∧
      IsMultiplyPretransitive G (CosetGraph.Vertex D) 3 ∧ Nat.card G = 8160 := by
  let D := cosetData S b hb hbout
  have he : Nat.card (CosetGraph.edgeStabilizer D) = 30 := by
    change Nat.card (CosetGraph.edgeStabilizer (cosetData S b hb hbout)) = 30
    rw [hedge, ← inf_subgroupOf_left, Nat.card_congr (subgroupOfEquivOfLe
      (show S.H1 ⊓ S.H2 ≤ S.H1 from inf_le_left)).toEquiv]
    exact overlap_card S
  exact CosetGraph.consequences D
    (CosetGraph.generation_of_index_two D S.H2 hb2 (overlap_index_two S) S.generated)
    htwo h hh hcube (point_card S) he

theorem faithful (b : G) (hb : b * b = 1) (hbout : b ∉ S.H1)
    (hedge : CosetGraph.edgeStabilizer (cosetData S b hb hbout) = S.H2.subgroupOf S.H1)
    (hdis : Disjoint (S.H2.subgroupOf S.H1) (pCore 2 S.H1)) :
    FaithfulSMul G (CosetGraph.Vertex (cosetData S b hb hbout)) := by
  let : (pCore 2 S.H1).Normal := pCore_normal
  apply CosetGraph.faithful_of_self_centralizing _ (pCore 2 S.H1)
  · exact S.core_centralizer.le
  · rw [hedge]
    exact hdis

end SourceData
end Sporadic.Janko3.SourceRecognition.Seventeen
