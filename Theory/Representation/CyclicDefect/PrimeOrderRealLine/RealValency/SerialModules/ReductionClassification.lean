module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification.DegreeOne

/-!
# Exhaustive assembly from constituent support and common-simple rigidity

Choose a simple submodule of an arbitrary indecomposable reduction and identify
it with an incident edge. The supplied vertex family has an indecomposable
member containing that same edge; common-simple rigidity identifies the two
reductions. This argument uses no common cyclic ordering or duality hypothesis.

This is a conditional assembly for Feit VII.2.25, printed pp.280,304.
Constituent support and the Green-correspondent uniqueness step remain explicit
premises and must be proved at the source application.
-/

public section
namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification

variable {p m n : ℕ} {K G : Type*} [Field K] [Group G] [Finite G]
    {d : ModularBlock.PrimeBlockConstruction.PrimeCongruenceBlockData p G}
    {L : CyclicRootLift K m} {t : Tree d.chi d.block p n L}
    {r : CompatibleRoots d K m} {v : {i // i ∈ d.block}}

/-- Exhaustive reduction classification, conditional on the two separately
stated source obligations. The original reduction is only assumed indecomposable. -/
theorem classify_of_simpleSupport_of_commonSimpleRigidity (a : VertexSeries t r v)
    (hp : p ≠ 1) (hs : SimpleSupport t r v) (hu : CommonSimpleRigidity t r v)
    (X : OrdinaryLattice d v.val)
    (hX : Module.IsIndecomposable (MonoidAlgebra K G) (X.reduction r).asModule) :
    ∃ e : ↥(t.incident v), Nonempty ((X.reduction r).Equiv ((a.lattice e).reduction r)) := by
  obtain ⟨e, f, hf⟩ := exists_incident_simple_embedding_of_support hs X hX
  obtain ⟨g, hg⟩ := vertex_edge_embedding a e
  exact ⟨e, hu X (a.lattice e) hX (vertex_reduction_isIndecomposable a hp e) e f hf g hg⟩

end Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification
