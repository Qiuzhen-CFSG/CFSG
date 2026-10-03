module

public import Theory.Representation.CompleteReducibility
public import Theory.Representation.RepMap
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Projection

/-!
# Complement models for injective intertwiners

For finite groups in characteristic zero, an injective intertwiner identifies
its source with an invariant direct summand. Maschke's theorem supplies an
invariant complement. Putting that complement in finite coordinates gives an
actual representation whose trace is the difference of the original traces.

This is the complement step in descent of virtual ordinary characters;
see Serre, *Linear Representations of Finite Groups*, Chapters 1 and 12.
-/

public section

open scoped MonoidAlgebra
noncomputable section
namespace Representation

set_option backward.isDefEq.respectTransparency false in
/-- Realize the trace difference of a representation and an embedded
subrepresentation on a standard finite coordinate space. -/
theorem exists_complement_model_of_injective
    {K G V W : Type*} [Field K] [CharZero K] [Group G] [Finite G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K G V) (σ : Representation K G W)
    (i : σ.IntertwiningMap ρ) (hi : Function.Injective i) :
    ∃ k, ∃ τ : Representation K G (Fin k → K), ∀ g,
      LinearMap.trace K _ (τ g) = LinearMap.trace K V (ρ g) -
        LinearMap.trace K W (σ g) := by
  classical
  let : IsSemisimpleModule K[G] ρ.asModule :=
    ρ.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
      (Or.inl (ringChar.eq_zero (R := K)))
  obtain ⟨M, hM⟩ := exists_isCompl i.range.asSubmodule
  let S : Subrepresentation ρ := Subrepresentation.ofSubmodule' M
  have hcompl : IsCompl i.range.toSubmodule S.toSubmodule := by
    exact (Submodule.isCompl_restrictScalars_iff K).mpr hM
  let e := Submodule.prodEquivOfIsCompl i.range.toSubmodule S.toSubmodule hcompl
  have hconj (g : G) : e.symm.conj (ρ g) =
      LinearMap.prodMap (i.range.toRepresentation g) (S.toRepresentation g) := by
    apply LinearMap.ext
    intro x
    apply e.injective
    simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
      LinearEquiv.apply_symm_apply]
    change ρ g (↑x.1 + ↑x.2) = ρ g ↑x.1 + ρ g ↑x.2
    exact map_add (ρ g) _ _
  let j : W ≃ₗ[K] i.range.toSubmodule := LinearEquiv.ofInjective i.toLinearMap hi
  have hj (g : G) : j.conj (σ g) = i.range.toRepresentation g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change i (σ g (j.symm x)) = ρ g ↑x
    rw [i.isIntertwining]
    exact congrArg (ρ g) (congrArg Subtype.val (j.apply_symm_apply x))
  have htrace (g : G) : LinearMap.trace K V (ρ g) =
      LinearMap.trace K W (σ g) + LinearMap.trace K S.toSubmodule (S.toRepresentation g) := by
    rw [← LinearMap.trace_conj' (ρ g) e.symm, hconj, LinearMap.trace_prodMap',
      ← hj, LinearMap.trace_conj']
  let b := Module.finBasis K S.toSubmodule
  let τ : Representation K G (Fin (Module.finrank K S.toSubmodule) → K) :=
    b.equivFun.conjRingEquiv.toMonoidHom.comp S.toRepresentation
  refine ⟨_, τ, fun g => ?_⟩
  change LinearMap.trace K _ (b.equivFun.conj (S.toRepresentation g)) = _
  rw [LinearMap.trace_conj', htrace]
  abel
end Representation
