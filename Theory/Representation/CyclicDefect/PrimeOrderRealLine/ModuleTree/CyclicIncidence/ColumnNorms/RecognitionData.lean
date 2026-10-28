module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.ColumnNorms.Restriction
public import Theory.Representation.CyclicDefect.ProjectivePairing.LiftComparison.Regular
public import Theory.Representation.KrullSchmidt

/-!
# Recognizing the principal projective attached to a supplied column

The simple module, projective module and integral lift are actual
representations. Indecomposability and a surjection onto the supplied simple
module identify the principal projective. Its ordinary character must agree
with the supplied column on every element. Existence of this data is the
separate modular-reduction and reciprocity theorem, Feit I.16--17.

The proved nonvanishing consequence uses the positive dimension of the
actual lifted module. No cyclic incidence or coefficient bound is included
in the recognition data. This interface allows the recognition proof and
Feit VII.5.6's conditional restriction proof to proceed independently.
-/

public section
noncomputable section
open scoped BigOperators Classical

namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.ColumnNorms
open ModularBlock.PrimeBlockConstruction
variable {p : ℕ} {G : Type*} [Group G] [Finite G]
    {K : Type*} [Field K] {m n : ℕ}
    {d : PrimeCongruenceBlockData p G}
    {residue : Localization.AtPrime d.primeIdeal →+* K}
    {L : CyclicRootLift K m}

/-- Recognition of a supplied projective column as the principal projective
for its supplied simple module. No coefficient bound or cyclic conclusion
is assumed. The ordinary equality is on all elements, not only regular ones. -/
structure PrincipalColumn (a : Decomposition d residue L n) (e : Fin n) where
  indecomposable : Module.IsIndecomposable (MonoidAlgebra K G) (a.projective e).rep.asModule
  head : Representation.IntertwiningMap (a.projective e).rep (a.rep e)
  head_surjective : Function.Surjective head
  lift : ProjectivePairing.IntegralLift L (a.projective e).rep
  ordinary_eq : ∀ g : G, lift.complexRep.character g =
    ordinarySum d (fun v => a.multiplicity v e) (ConjClasses.mk g)

/-- A recognized principal column has a nonzero ordinary constituent. -/
theorem PrincipalColumn.exists_nonzero (a : Decomposition d residue L n)
    {e : Fin n} (A : PrincipalColumn a e) : ∃ v, a.multiplicity v e ≠ 0 := by
  have : Nontrivial (a.projective e).rep.asModule := A.indecomposable.1
  have : Nontrivial (Fin (a.projective e).degree → K) :=
    Function.Injective.nontrivial (a.projective e).rep.asModuleEquiv.injective
  have : Nontrivial (Fin A.lift.degree → K) :=
    Function.Injective.nontrivial A.lift.reduction.toLinearEquiv.symm.injective
  have hdegree : 0 < A.lift.degree := by
    simpa using (Module.finrank_pos (R := K) (M := Fin A.lift.degree → K))
  by_contra hn
  push Not at hn
  have h := A.ordinary_eq 1
  have hz : (A.lift.degree : ℂ) = 0 := by
    simpa [ordinarySum_apply, hn, Representation.character] using h
  have : A.lift.degree = 0 := by exact_mod_cast hz
  omega

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.ColumnNorms
