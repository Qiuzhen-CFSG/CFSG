module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.ConjugateGraph
public import Theory.GroupTheory.GraphUniquenessSystem

/-!
# Local generation data for the J₂ subgroup graph

This is the source interface for the uniqueness system in Aschbacher,
*Sporadic Groups* (1994), 47.10, pp.266–267. The remaining inputs are a
neighbor Y of X, a local subgroup K, transitivity of N_G(X) on the neighbors
of X, and the three subgroup generation identities of condition (U).

The action, normalizer identification and graph preservation have already
been proved in `ConjugateGraph`. Neighbor transitivity gives edge transitivity
by moving one endpoint to X. These results assemble the full uniqueness
system; in the simple source group its faithfulness is discharged as well.
No local generation datum is assumed to follow from J₂-type here.
-/

@[expose] public section

open Subgroup Theory.GroupTheory.GraphUniquenessSystem

namespace CFSG.Quasithin.Janko23.J2Recognition
variable {G : Type*} [Group G] [Finite G]

/-- The remaining local subgroup and generation inputs for the source graph. -/
structure LocalData (D : Seed G) where
  y : D.Vertex
  adjacent : D.graph.Adj D.base y
  K : Subgroup G
  neighbors : ∀ v : D.Vertex, D.graph.Adj D.base v →
    ∃ k : normalizer (D.X : Set G), (k : G) • y = v
  local_orbit : ∃ k : K, (k : G) • D.base = y
  generate : K ⊔ normalizer (D.X : Set G) = ⊤
  vertex_generate : edgeFixer G D.base y ⊔ (K ⊓ normalizer (D.X : Set G)) =
    normalizer (D.X : Set G)
  local_generate : (K ⊓ edgeStabilizer G D.base y) ⊔
    (K ⊓ normalizer (D.X : Set G)) = K

namespace LocalData
variable {D : Seed G} (L : LocalData D)

/-- Assemble condition (U) with the literal conjugation action and normalizers. -/
def toSystem (hf : ∀ g : G, (∀ A : D.Vertex, g • A = A) → g = 1) :
    System G D.Vertex where
  graph := D.graph
  H := L.K
  x := D.base
  y := L.y
  adjacent := L.adjacent
  preserves := D.preserves
  faithful := hf
  vertex_transitive := D.transitive
  edge_transitive a b hab := by
    obtain ⟨g, hg⟩ := D.transitive a
    have hnear := D.preserves g⁻¹ hab
    have hx : g⁻¹ • a = D.base := by rw [← hg, inv_smul_smul]
    rw [hx] at hnear
    obtain ⟨k, hk⟩ := L.neighbors _ hnear
    have hkx : (k : G) • D.base = D.base := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [D.stabilizer_eq_normalizer]
      exact k.property
    refine ⟨g * k, Or.inl ⟨?_, ?_⟩⟩
    · rw [mul_smul, hkx, hg]
    · rw [mul_smul, hk, smul_inv_smul]
  local_orbit := L.local_orbit
  generate := by
    rw [D.stabilizer_eq_normalizer]
    exact L.generate
  vertex_generate := by
    rw [D.stabilizer_eq_normalizer]
    exact L.vertex_generate
  local_generate := by
    rw [D.stabilizer_eq_normalizer]
    exact L.local_generate

/-- For a simple source group, the graph action needs no additional faithfulness premise. -/
def simpleSystem [IsSimpleGroup G] : System G D.Vertex := L.toSystem D.faithful

end LocalData
end CFSG.Quasithin.Janko23.J2Recognition
