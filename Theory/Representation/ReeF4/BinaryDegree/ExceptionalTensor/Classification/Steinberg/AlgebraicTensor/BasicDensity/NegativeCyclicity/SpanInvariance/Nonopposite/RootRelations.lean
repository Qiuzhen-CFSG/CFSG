module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Nonopposite.PolynomialTransfer
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Triangular
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Nonopposite.RootRelations.PositiveExchanges
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Nonopposite.RootRelations.SimultaneousTransport

/-!
# Actual F₄ carrier exchanges for nonopposite short-root pairs

A positive root and a negative short root which are not opposite are linearly
independent. A common Weyl word carries both into the fixed positive system.
The integral A₂ and B₂ calculations give the positive carrier exchanges over
the algebraically closed field. Simultaneous carrier conjugation transports
them back, retaining the short sum root, the possible quadratic correction,
and commutation when the sum is absent or long.

These are identities of points of the actual algebraic F₄ carrier, before
applying a representation. No coefficient-bracket or highest-weight premise
is used. Source: Steinberg, Representations of Algebraic Groups, Nagoya Math.
J. 22 (1963), §§2,4,10 and 11.1(1), DOI 10.1017/S0027763000011016.
-/

public section
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.SpanInvariance.Nonopposite
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
local instance nonoppositeRootRelationsNeg : InvolutiveNeg F4Chevalley.Root :=
  typeF4RootPairing.indexNeg

/-- The unconditional characteristic-two carrier exchange for every
nonopposite positive/negative-short root pair. -/
theorem nonopposite_root_exchange (r : PositiveRoot) (s : ShortNegativeRoot)
    (hne : s.val ≠ -r.val) : ShortRootExchange (F := F) r.val s.val := by
  have hli : LinearIndependent ℝ
      ![typeF4RootPairing.root r.val, typeF4RootPairing.root s.val] := by
    apply RootPairing.IsReduced.linearIndependent typeF4RootPairing
    · intro he
      exact s.property.2 (he ▸ r.property)
    · intro he
      apply hne
      apply typeF4RootPairing.root.injective
      rw [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
        RootPairing.reflection_apply_self, he, neg_neg]
  obtain ⟨w, hr, hs⟩ := exists_common_positive_word r.val s.val hli
  apply (shortRootExchange_word_iff w r.val s.val).mp
  exact positive_short_root_exchange _ _ hr hs
    ((WordRelations.ShortOperators.isShortRoot_reflectionWord w s.val).mpr s.property.1)

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.SpanInvariance.Nonopposite
