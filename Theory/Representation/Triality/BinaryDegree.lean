module

public import Theory.Representation.Triality.BinaryDegree.TensorDescent
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# The binary triality degree bound from restricted-weight classification

For the genuine D4 graph-field carrier `Standard.BinaryCarrier n hn`, the
restricted-weight tensor classification over algebraic closures of finite fields
implies the universal binary lower bound `24*n`. The Schur-field construction
preserves faithfulness and irreducibility, and `TensorDescent` treats every
Frobenius period and all basic-weight alternatives, including `n = 1`.

The classification premise below remains to be proved for this actual carrier.
Thus this is a conditional assembly theorem, not the unconditional triality
minimum. Identifying a universal algebraic-group model with the standard
geometric carrier is also required when constructing that premise by transport.
The auxiliary `Triality.Model` is not used.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, printed
p.356 (PDF p.367), and GLS3 §2.8 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
namespace Triality.BinaryDegree
open Representation.FrobeniusTensor
universe v

/-- The exact binary estimate follows once the restricted-weight tensor data
is constructed for every faithful irreducible on the genuine carrier. -/
theorem triality_binary_degree_ge_of_tensor_classification
    {n : ℕ} (hn : 0 < n)
    (hclassification : ∀
      (E : Type v) [Field E] [Finite E] [CharP E 2]
      (W : Type v) [AddCommGroup W] [Module (AlgebraicClosure E) W]
      [FiniteDimensional (AlgebraicClosure E) W]
      (σ : Representation (AlgebraicClosure E) (Triality.Standard.BinaryCarrier n hn) W),
      σ.IsIrreducible → Function.Injective σ → Nonempty (TensorData n σ))
    {V : Type v} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (Triality.Standard.BinaryCarrier n hn) V)
    [ρ.IsIrreducible] (hρ : Function.Injective ρ) :
    24 * n ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨hdata⟩ := hclassification (SchurField ρ) (AbsoluteSpace ρ)
    (absoluteRep ρ) inferInstance (absoluteRep_injective ρ hρ)
  exact binary_finrank_ge_of_tensorData ρ hn hdata

end Triality.BinaryDegree
