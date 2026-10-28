module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification.Preparation
public import Theory.Representation.IrreducibleTraceEquivalence

/-!
# The degree-one branch of reduction classification

Lattices affording the same degree-one ordinary character reduce to simple
one-dimensional representations. Their traces agree at the actual residue map,
and irreducible trace separation gives an intertwining equivalence. Thus the
exhaustive classification is already unconditional at a degree-one vertex,
including the principal vertex of the eleven-block.

This is the degree-one special case of Feit VII.2.25, printed p.280. It does
not require the general Green-correspondent rigidity theorem.
-/

public section
namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification

variable {p m n : ℕ} {K G : Type*} [Field K] [IsAlgClosed K] [Group G] [Finite G]
    {d : ModularBlock.PrimeBlockConstruction.PrimeCongruenceBlockData p G}
    {L : CyclicRootLift K m} {t : Tree d.chi d.block p n L}
    {r : CompatibleRoots d K m} {v : {i // i ∈ d.block}}

/-- Reductions of degree-one ordinary lattices with the same character are equivalent. -/
theorem reduction_equiv_of_degree_one (X Y : OrdinaryLattice d v.val) (hX : X.degree = 1) :
    Nonempty ((X.reduction r).Equiv (Y.reduction r)) := by
  have hXY : X.degree = Y.degree := by
    exact_mod_cast X.character_one.symm.trans Y.character_one
  have hY : Y.degree = 1 := hXY.symm.trans hX
  let : IsIrreducible (X.reduction r) := by
    rw [irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
    apply is_simple_module_of_finrank_eq_one (K := K)
    change Module.finrank K (Fin X.degree → K) = 1
    simp [hX]
  let : IsIrreducible (Y.reduction r) := by
    rw [irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
    apply is_simple_module_of_finrank_eq_one (K := K)
    change Module.finrank K (Fin Y.degree → K) = 1
    simp [hY]
  exact (character_eq_iff_equiv_of_irreducible (X.reduction r) (Y.reduction r)).mp
    (reduction_character_eq X Y)

/-- Complete classification at a degree-one vertex, without an indecomposability premise. -/
theorem classify_of_degree_one (a : VertexSeries t r v) (hp : p ≠ 1)
    (hv : d.chi v.val (ConjClasses.mk 1) = 1) (X : OrdinaryLattice d v.val) :
    ∃ e : ↥(t.incident v), Nonempty ((X.reduction r).Equiv ((a.lattice e).reduction r)) := by
  have hX : X.degree = 1 := by
    have h := X.character_one
    rw [hv] at h
    exact_mod_cast h.symm
  have hpos : 0 < (t.incident v).card := by
    rw [t.incident_card_eq_one hp v hv]
    decide
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  exact ⟨⟨e, he⟩, reduction_equiv_of_degree_one X (a.lattice ⟨e, he⟩) hX⟩

end Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification
