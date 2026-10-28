module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification.Preparation
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification.SimpleSupport.TraceComparison
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification.SimpleSupport.SeriesCharacter

/-!
# Simple support of arbitrary ordinary-lattice reductions

The supplied vertex series contains each incident simple once. Any other
lattice affording the same ordinary character has the same trace after the
literal residue map. Extend the prescribed simple submodule to an actual
composition series of this other reduction. Trace independence forces every
incident simple to occur, and the exact ordinary degree sum leaves no room for
additional factors. Empty incidence is excluded by the nonzero submodule.

Source: Feit, *The Representation Theory of Finite Groups*, I.17, VII.2.19,
and the simple-submodule step of VII.2.25 on printed p.304. The earlier vertex
series is an explicit input; its existence and common-simple rigidity are
separate source results.
-/

public section
noncomputable section
open scoped BigOperators Classical

namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification
universe u w
variable {K : Type u} {G : Type w} [Field K] [IsAlgClosed K] [Group G] [Finite G]
    {p m n : ℕ}
    {d : ModularBlock.PrimeBlockConstruction.PrimeCongruenceBlockData p G}
    {L : CyclicRootLift K m} {t : Tree d.chi d.block p n L}
    {r : CompatibleRoots d K m} {v : {i // i ∈ d.block}}

omit [IsAlgClosed K] in
private theorem vertex_character_sum (a : VertexSeries t r v) (e : ↥(t.incident v)) :
    ((a.lattice e).reduction r).character = ∑ f : ↥(t.incident v), (t.rep f.val).character := by
  rw [(a.series e).character_sum]
  calc
    ∑ i, ((a.series e).factor i).character =
        ∑ i, (t.rep (a.ordering e i).val).character := by
      apply Finset.sum_congr rfl
      intro i _
      exact char_iso (Classical.choice (a.factor_equiv e i))
    _ = _ := (a.ordering e).sum_comp (fun f : ↥(t.incident v) => (t.rep f.val).character)

/-- Every simple submodule of an arbitrary vertex reduction is an incident
edge. The supplied series fixes the multiplicity-free character and dimension;
no indecomposability, seriality or simple-socle premise is imposed on `X`. -/
theorem simpleSupport_of_vertexSeries (a : VertexSeries t r v) (hp : p ≠ 1) :
    SimpleSupport t r v := by
  intro X U hU
  let := hU
  have : Nontrivial U.toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial U.toRepresentation
  have hpos : 0 < X.degree := by
    have hsub := Module.finrank_pos (R := K) (M := U.toSubmodule)
    have hle := Submodule.finrank_le U.toSubmodule
    simpa only [Module.finrank_pi, Fintype.card_fin] using lt_of_lt_of_le hsub hle
  have hnonempty : (t.incident v).Nonempty := by
    by_contra h
    have hd := lattice_degree_eq_incident_sum t hp v X
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hd
    simp only [Finset.sum_empty] at hd
    omega
  obtain ⟨e, he⟩ := hnonempty
  have hc : (X.reduction r).character = ∑ f : ↥(t.incident v), (t.rep f.val).character :=
    (reduction_character_eq X (a.lattice ⟨e, he⟩)).trans (vertex_character_sum a ⟨e, he⟩)
  obtain ⟨q, F, hF⟩ := CompositionSeriesTrace.exists_finiteSeries (FDRep.of U.quotientRepresentation)
  let M : Fin (q + 1) → FDRep K G := Fin.cons (FDRep.of U.toRepresentation) F
  let N : ↥(t.incident v) → FDRep K G := fun f => FDRep.of (t.rep f.val)
  have hseries : CompositionSeriesTrace.FiniteSeries (FDRep.of (X.reduction r)) M :=
    .step (FDRep.of (X.reduction r)) U hU hF
  have hN (f : ↥(t.incident v)) : IsIrreducible (N f).ρ := t.irreducible f.val
  have hne : Pairwise fun f g => IsEmpty (Equiv (N f).ρ (N g).ρ) := by
    intro f g hfg
    exact t.inequivalent (fun h => hfg (Subtype.ext h))
  have hchars : ∑ i, character (M i).ρ = ∑ f, character (N f).ρ :=
    hseries.character_sum.symm.trans hc
  have hdims : ∑ i, Module.finrank K (M i) = ∑ f, Module.finrank K (N f) := by
    rw [← hseries.dimension_sum]
    change Module.finrank K (Fin X.degree → K) =
      ∑ f : ↥(t.incident v), Module.finrank K (Fin (t.degree f.val) → K)
    simp only [Module.finrank_pi, Fintype.card_fin]
    rw [lattice_degree_eq_incident_sum t hp v X]
    exact (Finset.sum_coe_sort (t.incident v) t.degree).symm
  exact CompositionSeriesTrace.support_of_equal_sums M N hseries.simple hN hne hchars hdims 0
end Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification
