module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.FourGeneration
public import Theory.GroupTheory.GraphUniquenessSystem.Recognition

/-!
# Recognition using the native octad base

An equivalence with the actual octad–trio–sextet uniqueness system extends
uniquely to a group isomorphism with M24. The target's base and simplicity
are discharged here. Compatibility with the prescribed vertex and plane
isomorphisms is retained. The rigidity variant uses the general local
comparison theorem.

These are model recognition theorems, not the source §41.4 comparison.
Constructing the source coset system and its local equivalence from the
marked normalizer data remains necessary for the source uniqueness theorem.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 13.2(4–5),
printed p.210, and 41.4–41.5, pp.221–222.
-/

public noncomputable section
open Sporadic.Mathieu
namespace Sporadic.Mathieu.M24LocalGeometry.OctadGraph
open Theory.GroupTheory.GraphUniquenessSystem
variable {G V : Type*} [Group G] [MulAction G V] {U : System G V}

/-- Exercise 13.2(5), retaining the two prescribed local restrictions. -/
theorem existsUnique_mulEquiv_of_equivalence (s : Similarity U system)
    (hs : s.IsEquivalence) :
    ∃! e : G ≃* M24,
      (∀ a : U.vertexGroup, e a = (s.vertexIso a : M24)) ∧
      (∀ a : U.H, e a = (s.localIso a : M24)) := by
  let : IsSimpleGroup M24 := m24_isSimpleGroup
  exact s.existsUnique_mulEquiv_of_isEquivalence_of_isBase hs system_isBase

/-- The 37.9 criterion with the native model base discharged. -/
theorem existsUnique_mulEquiv_of_rigid (s : Similarity U system)
    (hr : AutomorphismRigid (U.H.subgroupOf U.edgeGroup)) :
    ∃! e : G ≃* M24,
      (∀ a : U.vertexGroup, e a = (s.vertexIso a : M24)) ∧
      (∀ a : U.H, e a = (s.localIso a : M24)) :=
  existsUnique_mulEquiv_of_equivalence s (s.isEquivalence_of_rigid hr)

end Sporadic.Mathieu.M24LocalGeometry.OctadGraph
