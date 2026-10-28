module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.Coordinates
public import Theory.Representation.FactorDegreeFiltration
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.Duality

/-!
# Simple quotient degrees from the two concrete induced filtrations

An invariant filtration with irreducible factors of degrees 1, 10, 34 and 98
bounds every simple quotient, even when the extensions do not split. We apply
that argument to the literal quotients of the two Hermitian point-module
inductions, using the checked right-coset intertwining equivalence.

The checked Hermitian filtration supplies the first witness; finite-dimensional
duality supplies the second. Thus `smallInducedHeads` proves the bound for both
literal induced modules without additional hypotheses. The conditional assembly
theorem remains available separately.

Source: the degree-table step in Guralnick--Malle I, Proposition 5.1,
pp.15--16, used in Theorem 6.6/Table 6.7 and Aschbacher--Smith, Chapter K,
printed pp.451--452 and 457. The factor degrees follow from the checked invariant
flag and full matrix algebras of its successive quotients.
-/

@[expose] public noncomputable section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule
namespace InducedHeads

/-- The four irreducible factor degrees in the checked induced filtrations. -/
def factorDegrees : Set ℕ := {1, 10, 34, 98}

/-- A coordinate filtration controls each literal maximal quotient of the
original induced module. No splitting of the filtration is used. -/
theorem quotient_finrank_mem_of_coordinateFiltration (b : Bool) {D : Set ℕ}
    (hfiltration : FactorDegreeFiltration D (coordinateAction b))
    (N : Subrepresentation (Models.induced b)) (hN : IsCoatom N) :
    Module.finrank (ZMod 2) (Models.InducedSpace b ⧸ N.toSubmodule) ∈ D := by
  let : IsIrreducible N.quotientRepresentation :=
    SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN
  let q : (Models.induced b).IntertwiningMap N.quotientRepresentation :=
    ⟨N.toSubmodule.mkQ, fun _ => rfl⟩
  let f := q.comp (inducedCoordinateEquiv b).symm.toIntertwiningMap
  apply hfiltration.finrank_mem f
  intro hf
  let : Nontrivial (Models.InducedSpace b ⧸ N.toSubmodule) :=
    Subrepresentation.irreducible_module_nontrivial N.quotientRepresentation
  obtain ⟨x, hx⟩ := exists_ne (0 : Models.InducedSpace b ⧸ N.toSubmodule)
  obtain ⟨v, hv⟩ := N.toSubmodule.mkQ_surjective x
  have h := congrArg (fun t => t (inducedCoordinateEquiv b v)) hf
  change q ((inducedCoordinateEquiv b).symm (inducedCoordinateEquiv b v)) = 0 at h
  rw [Representation.Equiv.symm_apply_apply] at h
  exact hx (hv.symm.trans h)

end InducedHeads

/-- Assembly of the requested bound from independently constructed filtrations
of the Hermitian induction and the dual-Hermitian induction. -/
theorem smallInducedHeads_of_coordinateFiltrations
    (hfalse : FactorDegreeFiltration InducedHeads.factorDegrees
      (InducedHeads.coordinateAction false))
    (htrue : FactorDegreeFiltration InducedHeads.factorDegrees
      (InducedHeads.coordinateAction true)) : SmallInducedHeads := by
  intro b N hN
  have hfiltration : FactorDegreeFiltration InducedHeads.factorDegrees
      (InducedHeads.coordinateAction b) := by
    cases b
    · exact hfalse
    · exact htrue
  have hd := InducedHeads.quotient_finrank_mem_of_coordinateFiltration b hfiltration N hN
  simp only [InducedHeads.factorDegrees, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  omega

/-- Every simple quotient of either concrete Hermitian nine-space induction
has binary dimension one, ten, or greater than thirty. -/
theorem smallInducedHeads : SmallInducedHeads :=
  smallInducedHeads_of_coordinateFiltrations
    InducedHeads.HermitianFiltration.filtration
    (coordinateFiltration_true_of_false InducedHeads.HermitianFiltration.filtration)

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule
