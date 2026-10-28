module

public import Theory.Representation.EndFieldTrace
public import Theory.Representation.IrreducibleTraceEquivalence
public import Theory.Representation.SemilinearConjugation
public import Theory.FieldTheory.SpanningFrobeniusPeriod
public import Mathlib.Algebra.Algebra.ZMod

/-!
# The Schur field and the exact Frobenius period

For an irreducible representation over a prime field, the degree of its actual
endomorphism field is the least positive Frobenius period of its absolutely
irreducible scalar extension. The dimension over the prime field is this degree
times the dimension of the extended representation.

The traces span the endomorphism field. Thus Frobenius fixes those traces
exactly at multiples of the field degree. Over an algebraically closed field,
equality of irreducible characters is equivalent to an actual intertwining
equivalence. A choice of basis constructs the coefficient twist; the resulting
period criterion is independent of that choice.

This is the Schur-field part of GLS3, Remark 2.8.8. No classification of the
representations of the acting group is used here.
-/

open scoped MonoidAlgebra TensorProduct

public noncomputable section

namespace Representation

section Twist

variable {K G W : Type*} [Field K] [IsAlgClosed K] [Monoid G]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  (p : ℕ) [Fact p.Prime] [CharP K p]

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- A choice of basis realizes Frobenius as a semilinear equivalence. -/
@[expose] def frobeniusSemilinearEquiv (r : ℕ) :
    LinearEquiv (iterateFrobeniusEquiv K p r : K →+* K)
      (σ' := ((iterateFrobeniusEquiv K p r).symm : K →+* K)) W W :=
  (Module.finBasis K W).equivFun.trans
    ((coordinateSemilinearEquiv (iterateFrobeniusEquiv K p r) _).trans
      (Module.finBasis K W).equivFun.symm)

/-- The actual coefficient Frobenius twist, transported back to the carrier. -/
@[expose] def frobeniusConjugate (r : ℕ) (σ : Representation K G W) :
    Representation K G W :=
  semilinearConjugate (iterateFrobeniusEquiv K p r) σ (frobeniusSemilinearEquiv p r)

theorem frobeniusConjugate_isIrreducible (r : ℕ) (σ : Representation K G W)
    [IsIrreducible σ] : IsIrreducible (frobeniusConjugate p r σ) :=
  isIrreducible_semilinearConjugate _ _ _ inferInstance

theorem character_frobeniusConjugate (r : ℕ) (σ : Representation K G W) (g : G) :
    (frobeniusConjugate p r σ).character g = σ.character g ^ (p ^ r) :=
  character_semilinearConjugate _ _ _ g

end Twist

section Schur

variable {G V : Type*} [Monoid G] [AddCommGroup V]
  (p : ℕ) [Fact p.Prime] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
  (ρ : Representation (ZMod p) G V) [IsIrreducible ρ]

/-- The degree of the actual endomorphism field, rather than a field label. -/
@[expose] def schurDegree : ℕ :=
  Module.finrank (ZMod p) (Module.End (ZMod p)[G] ρ.asModule)

theorem schurDegree_pos : 0 < schurDegree p ρ := by
  let : Module.Finite (ZMod p) (Module.End (ZMod p)[G] ρ.asModule) :=
    Module.Finite.of_finite
  exact Module.finrank_pos

/-- The Schur model is finite-dimensional over its endomorphism field. -/
instance endFieldRep_finiteDimensional :
    FiniteDimensional (Module.End (ZMod p)[G] ρ.asModule) ρ.asModule := by
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod p) ρ.asModule)
  exact Module.Finite.of_finite

/-- The trace period is exactly the degree of the endomorphism field. -/
theorem endFieldRep_trace_frobenius_iff (r : ℕ) :
    (∀ g, LinearMap.trace (Module.End (ZMod p)[G] ρ.asModule) ρ.asModule
      (ρ.endFieldRep g) ^ (p ^ r) =
      LinearMap.trace (Module.End (ZMod p)[G] ρ.asModule) ρ.asModule
        (ρ.endFieldRep g)) ↔ schurDegree p ρ ∣ r :=
  FiniteField.forall_pow_eq_self_iff_finrank_dvd_of_span p _
    (span_range_endFieldRep_trace ρ) r

variable (K : Type*) [Field K] [IsAlgClosed K]
  [Algebra (Module.End (ZMod p)[G] ρ.asModule) K] [CharP K p]

omit [IsAlgClosed K] [CharP K p] in
/-- The scalar-dimension tower for the absolutely irreducible Schur model. -/
theorem finrank_eq_schurDegree_mul :
    Module.finrank (ZMod p) V = schurDegree p ρ *
      Module.finrank K (K ⊗[Module.End (ZMod p)[G] ρ.asModule] ρ.asModule) := by
  let E := Module.End (ZMod p)[G] ρ.asModule
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod p) ρ.asModule)
  let : Module.Finite E ρ.asModule := Module.Finite.of_finite
  rw [Module.finrank_baseChange, schurDegree,
    Module.finrank_mul_finrank (ZMod p) E ρ.asModule]
  exact ρ.asModuleEquiv.finrank_eq.symm

/-- Frobenius fixes the isomorphism class of the extended Schur model precisely
at multiples of the Schur degree. The equivalence is a genuine intertwiner. -/
theorem endFieldRep_frobenius_equiv_iff (r : ℕ) :
    Nonempty ((extendScalars K ρ.endFieldRep).Equiv
      (frobeniusConjugate p r (extendScalars K ρ.endFieldRep))) ↔
        schurDegree p ρ ∣ r := by
  let E := Module.End (ZMod p)[G] ρ.asModule
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod p) ρ.asModule)
  let : Module.Finite E ρ.asModule := Module.Finite.of_finite
  let : IsAbsolutelyIrreducible ρ.endFieldRep := endFieldRep_isAbsolutelyIrreducible ρ
  let : IsIrreducible (extendScalars K ρ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep K
  let : IsIrreducible (frobeniusConjugate p r (extendScalars K ρ.endFieldRep)) :=
    frobeniusConjugate_isIrreducible p r _
  rw [← character_eq_iff_equiv_of_irreducible,
    ← endFieldRep_trace_frobenius_iff p ρ r]
  rw [funext_iff]
  apply forall_congr'
  intro g
  rw [character_frobeniusConjugate]
  change LinearMap.trace K _ ((ρ.endFieldRep g).baseChange K) =
    LinearMap.trace K _ ((ρ.endFieldRep g).baseChange K) ^ (p ^ r) ↔ _
  rw [LinearMap.trace_baseChange, ← map_pow, (algebraMap E K).injective.eq_iff]
  exact eq_comm

end Schur
end Representation
