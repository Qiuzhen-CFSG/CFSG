module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.Graph
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.Transitivity

/-!
# The fixed HS permutation normalizer preserves its orbital graph

The stabilizer of zero is transitive on the 77 distinct nonneighbors: the
words below, in exactly `OrderCertificate.gen1`, send vertex 1 to each such
vertex. Lean checks every image, while `H1_le`, `next0_fix` and
`H0_eq_generated` put these words in the actual HS carrier and fix zero.
Transitivity of that carrier transports this result to every vertex.

If a normalizing permutation sent a nonedge to an edge, conjugating these
stabilizer elements would send all 77 nonneighbors injectively into the 22
neighbors of the image vertex. The cardinality contradiction proves
preservation of nonedges; applying it to the inverse proves preservation of
edges. This uses no graph automorphism order or outer-automorphism assertion.

Source: GLS3, Table 5.3m, printed p.274, Note 1 (the degree-100 rank-three
action); the exact ATLAS HSG1-p100B0 carrier and action convention are in
`HS.lean`. The candidate words are copied by vertex label from
`source/graph_witnesses.json`, produced by `source/discover_graph.py`.
-/

namespace Sporadic.LeechRelated.HS.NormalizerIndex
open OrderCertificate Theory.GroupTheory
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private def nonneighborWord (x : Fin 100) : List (Fin 17) :=
  match x.val with
  | 2 => [0, 12]
  | 3 => [14]
  | 5 => [12, 4]
  | 6 => [1]
  | 7 => [10, 4]
  | 13 => [1, 4]
  | 14 => [0, 2]
  | 15 => [12]
  | 16 => [6, 6]
  | 17 => [12, 5]
  | 18 => [0, 10]
  | 19 => [13, 7]
  | 20 => [0, 4]
  | 21 => [9, 8]
  | 22 => [13]
  | 23 => [6, 8]
  | 24 => [6, 2]
  | 25 => [5, 0, 3]
  | 27 => [12, 3]
  | 29 => [9, 3]
  | 30 => [10, 1]
  | 31 => [8, 9]
  | 33 => [6, 0, 2]
  | 34 => [7, 1]
  | 35 => [1, 3, 1]
  | 36 => [13, 5]
  | 37 => [5]
  | 41 => [14, 2]
  | 42 => [0, 3]
  | 43 => [1, 8]
  | 45 => [0, 1]
  | 46 => [6, 1]
  | 48 => [3, 1]
  | 51 => [3, 2]
  | 53 => [2, 2]
  | 54 => [0, 10, 1]
  | 55 => [14, 4]
  | 56 => [6, 9]
  | 57 => [6]
  | 58 => [2]
  | 59 => [1, 7, 1]
  | 60 => [5, 1]
  | 61 => [15, 5]
  | 62 => [7, 5]
  | 63 => [7, 1, 3]
  | 64 => [1, 3]
  | 65 => [3, 5]
  | 68 => [0, 4, 1]
  | 69 => [8, 2]
  | 72 => [2, 4]
  | 73 => [3, 6]
  | 74 => [4]
  | 75 => [10, 6]
  | 76 => [10]
  | 77 => [5, 4]
  | 78 => [3]
  | 79 => [1, 12]
  | 80 => [7]
  | 81 => [13, 6]
  | 82 => [1, 12, 1]
  | 83 => [9, 0, 3]
  | 84 => [4, 7]
  | 85 => [9]
  | 86 => [1, 6]
  | 87 => [3, 3]
  | 88 => [4, 1]
  | 89 => [9, 1]
  | 90 => [13, 2]
  | 92 => [8, 5]
  | 93 => [1, 9]
  | 94 => [8]
  | 95 => [1, 1]
  | 96 => [12, 1]
  | 97 => [2, 6]
  | 98 => [2, 8]
  | 99 => [7, 2]
  | _ => []

private def nonneighborRep (x : Fin 100) : Equiv.Perm (Fin 100) :=
  evalWord gen1 (nonneighborWord x)

private theorem nonneighborRep_mem (x : Fin 100) : nonneighborRep x ∈ H1 :=
  ⟨nonneighborWord x, rfl⟩

private theorem nonneighborRep_apply (x : Fin 100) (hx : x ∈ nonneighbors 0) :
    nonneighborRep x 1 = x := by
  have h : ∀ y : Fin 100, y ∈ nonneighbors 0 → nonneighborRep y 1 = y := by
    apply allFin
    decide +kernel
  exact h x hx

private theorem H1_le_generated : H1 ≤ generated := by
  rw [← H0_eq_generated]
  exact H1_le

private theorem nonneighbors_zero_transitive (x y : Fin 100)
    (hx : x ∈ nonneighbors 0) (hy : y ∈ nonneighbors 0) :
    ∃ g ∈ generated, g 0 = 0 ∧ g x = y := by
  let a := nonneighborRep x
  let b := nonneighborRep y
  have ha : a ∈ H1 := nonneighborRep_mem x
  have hb : b ∈ H1 := nonneighborRep_mem y
  refine ⟨b * a⁻¹, H1_le_generated (H1.mul_mem hb (H1.inv_mem ha)), ?_, ?_⟩
  · exact next0_fix ⟨b * a⁻¹, H1.mul_mem hb (H1.inv_mem ha)⟩
  · change b (a⁻¹ x) = y
    rw [← nonneighborRep_apply x hx]
    simpa only [a, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using nonneighborRep_apply y hy

private theorem nonneighbors_transitive (v x y : Fin 100)
    (hx : x ∈ nonneighbors v) (hy : y ∈ nonneighbors v) :
    ∃ g ∈ generated, g v = v ∧ g x = y := by
  obtain ⟨a, ha⟩ := exists_apply_zero v
  let p : Equiv.Perm (Fin 100) := a
  have hp : p ∈ graphGroup := generated_le_graphGroup a.property
  have hpi : p⁻¹ ∈ graphGroup := graphGroup.inv_mem hp
  have hzero : p⁻¹ v = 0 := by rw [← ha]; exact p.symm_apply_apply 0
  have hpre (z : Fin 100) (hz : z ∈ nonneighbors v) :
      p⁻¹ z ∈ nonneighbors 0 := by
    rcases (mem_nonneighbors v z).mp hz with ⟨hne, hnot⟩
    apply (mem_nonneighbors 0 (p⁻¹ z)).mpr
    constructor
    · intro h
      apply hne
      apply p.symm.injective
      exact h.trans hzero.symm
    · have hi := mem_graphGroup_iff p⁻¹ |>.mp hpi v z
      rw [hzero] at hi
      exact fun h => hnot (hi.mp h)
  obtain ⟨g, hg, hg0, hgxy⟩ :=
    nonneighbors_zero_transitive (p⁻¹ x) (p⁻¹ y) (hpre x hx) (hpre y hy)
  refine ⟨p * g * p⁻¹,
    generated.mul_mem (generated.mul_mem a.property hg) (generated.inv_mem a.property), ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, hzero, hg0]
    exact ha
  · change p (g (p⁻¹ x)) = y
    rw [hgxy]
    exact p.apply_symm_apply y

private theorem normalizer_maps_nonneighbors (n : Equiv.Perm (Fin 100))
    (hn : n ∈ Subgroup.normalizer (generated : Set (Equiv.Perm (Fin 100))))
    (v x : Fin 100) (hx : x ∈ nonneighbors v) :
    n x ∈ nonneighbors (n v) := by
  rcases (mem_nonneighbors v x).mp hx with ⟨hne, _⟩
  apply (mem_nonneighbors (n v) (n x)).mpr
  refine ⟨fun h => hne (n.injective h), ?_⟩
  intro hadj
  have hmap : Set.MapsTo n (nonneighbors v) (neighbors (n v)) := by
    intro y hy
    obtain ⟨g, hg, hgv, hgxy⟩ := nonneighbors_transitive v x y hx hy
    have hc : n * g * n⁻¹ ∈ generated :=
      ((Subgroup.mem_normalizer_iff.mp hn) g).mp hg
    have hp := mem_graphGroup_iff (n * g * n⁻¹) |>.mp
      (generated_le_graphGroup hc) (n v) (n x)
    have h := hp.mpr hadj
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply, hgv, hgxy] at h
    exact (mem_neighbors (n v) (n y)).mpr h
  have hcard := Finset.card_le_card_of_injOn n hmap n.injective.injOn
  rw [nonneighbors_card, neighbors_card] at hcard
  omega

/-- Every permutation normalizing the defining HS subgroup preserves its graph. -/
public theorem normalizer_le_graphGroup :
    Subgroup.normalizer (HS.generated : Set (Equiv.Perm (Fin 100))) ≤ graphGroup := by
  intro n hn
  apply (mem_graphGroup_iff n).mpr
  have forward (p : Equiv.Perm (Fin 100))
      (hp : p ∈ Subgroup.normalizer (generated : Set (Equiv.Perm (Fin 100))))
      (x y : Fin 100) (hxy : adjacency x y) : adjacency (p x) (p y) := by
    by_contra h
    have hy : p y ∈ nonneighbors (p x) := by
      apply (mem_nonneighbors (p x) (p y)).mpr
      refine ⟨?_, h⟩
      intro heq
      have hyx : y = x := p.injective heq
      exact adjacency_irrefl x (hyx ▸ hxy)
    have hz := normalizer_maps_nonneighbors p⁻¹
      ((Subgroup.normalizer (generated : Set (Equiv.Perm (Fin 100)))).inv_mem hp)
      (p x) (p y) hy
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply, mem_nonneighbors] at hz
    exact hz.2 hxy
  intro x y
  constructor
  · intro h
    have hi := forward n⁻¹
      ((Subgroup.normalizer (generated : Set (Equiv.Perm (Fin 100)))).inv_mem hn)
      (n x) (n y) h
    simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using hi
  · exact forward n hn x y

end Sporadic.LeechRelated.HS.NormalizerIndex
