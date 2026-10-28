module

public import Theory.Representation.ReeF4.BinaryDegree.TensorDescent
public import Theory.SpecificGroups.ReeF4.Model
public import Theory.SpecificGroups.Tits.Presentation

/-!
# Binary degree reductions for Ree F4 and the Tits endpoint

The Ree estimate follows from the exceptional tensor classification over an
algebraic closure, including its Frobenius action on factor parameters.
The Schur-field construction preserves faithfulness and irreducibility, and
the proved tensor descent gives the multiplier `2*k+1` in binary dimension.
For the Tits endpoint, an absolute minimum passes through the same Schur
construction directly.

The two model-specific representation-theoretic inputs below are explicit
premises and have not yet been discharged. Thus these are conditional
assembly lemmas, not proofs of either universal model minimum. The endpoint
is `Tits.ParrottGroup`, not the full fixed-point group `ReeF4.Model 0`.
Finiteness needed by the absolute endpoint bound is supplied by the original
faithful binary action; no global finiteness theorem for the presentation is
needed here.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, printed
p.356 (PDF p.367), using GLS3 §2.8, especially 2.8.6(b) and 2.8.8.
-/

public section

namespace ReeF4.BinaryDegree

open Representation.FrobeniusTensor

universe v

/-- The binary Ree minimum follows from actual tensor data over algebraic
closures of finite fields. The classification premise still needs proof. -/
theorem ree_binary_degree_ge_of_tensor_classification
    (hclassification : ∀ (k : ℕ), 1 ≤ k →
      ∀ (E : Type v) [Field E] [Finite E] [CharP E 2]
        (W : Type v) [AddCommGroup W] [Module (AlgebraicClosure E) W]
        [FiniteDimensional (AlgebraicClosure E) W]
        (σ : Representation (AlgebraicClosure E) (Model k) W),
        σ.IsIrreducible → Function.Injective σ →
          Nonempty (TraceTensorData (2 * k + 1) 26 σ))
    {k : ℕ} (hk : 1 ≤ k) {V : Type v} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (Model k) V)
    [ρ.IsIrreducible] (hρ : Function.Injective ρ) :
    26 * (2 * k + 1) ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨hdata⟩ := hclassification k hk (SchurField ρ) (AbsoluteSpace ρ)
    (absoluteRep ρ) inferInstance (absoluteRep_injective ρ hρ)
  exact binary_finrank_ge_of_traceTensorData ρ (by omega) (by decide) hdata

/-- The absolute Tits minimum implies its binary minimum. The absolute
minimum is a separate premise for the actual Parrott carrier. -/
theorem tits_binary_degree_ge_of_absolute_minimum
    (hminimum : ∀ [Finite Tits.ParrottGroup]
      (E : Type v) [Field E] [Finite E] [CharP E 2]
      (W : Type v) [AddCommGroup W] [Module (AlgebraicClosure E) W]
      [FiniteDimensional (AlgebraicClosure E) W]
      (σ : Representation (AlgebraicClosure E) Tits.ParrottGroup W),
      σ.IsIrreducible → Function.Injective σ →
        26 ≤ Module.finrank (AlgebraicClosure E) W)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) Tits.ParrottGroup V)
    [ρ.IsIrreducible] (hρ : Function.Injective ρ) :
    26 ≤ Module.finrank (ZMod 2) V := by
  let : Finite Tits.ParrottGroup := finite_of_faithful_binary ρ hρ
  exact (hminimum (SchurField ρ) (AbsoluteSpace ρ) (absoluteRep ρ)
    inferInstance (absoluteRep_injective ρ hρ)).trans (absolute_finrank_le_binary ρ)

end ReeF4.BinaryDegree
