module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance

/-!
# Negative short-root cyclicity of exceptional basic factors

The first-degree negative short-root monomials on a basic highest vector span
the entire factor. The empty word makes this span nonzero. `SpanInvariance`
proves stability under every root operator using the short-root commutators,
local long-simple fixation, and Weyl reflections. `RestrictedBridge` proves
differential irreducibility by constructing and lifting an actual simple
differential quotient and applying raw highest-weight uniqueness. The only
remaining alternative for the span is therefore the whole space.

The final theorem uses the universal-version hypothesis and raw highest-weight
uniqueness, with no extra restricted-module premise. The reverse highest-weight
contract is unnecessary. The original conditional reduction is preserved.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §§2, 4 and the first part of 11.1(1), pp. 52–53;
DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

/-- The last cyclicity step, with the two restricted-module obligations explicit.
This is a conditional reduction, not the basic-factor cyclicity theorem. -/
theorem RootExpansion.shortNegativeSpan_eq_top_of_rootOperator_invariant
    {B : AlgebraicFactor F} (p : RootExpansion B.action) (v : B.Space) (hv : v ≠ 0)
    (hirr : ∀ W : Submodule F B.Space, p.IsRootOperatorInvariant W → W = ⊥ ∨ W = ⊤)
    (hstable : p.IsRootOperatorInvariant (p.shortNegativeSpan v)) :
    p.shortNegativeSpan v = ⊤ := by
  rcases hirr _ hstable with hbot | htop
  · have hm := p.mem_shortNegativeSpan v
    rw [hbot, Submodule.mem_bot] at hm
    exact (hv hm).elim
  · exact htop

/-- Negative short-root monomials in the actual first-degree coefficients span
a nonzero basic factor. Both differential irreducibility and invariance of
the word span are proved by the imported restricted-module results. -/
theorem RootExpansion.shortNegativeSpan_eq_top_of_basic_highestWeight [CharP F 2]
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (hhigh : ∀ (B C : AlgebraicFactor F) (a : Weight),
      HasHighestWeight B a → HasHighestWeight C a →
        AreEquivalentRepresentations B.action C.action)
    {B : AlgebraicFactor F} (p : RootExpansion B.action)
    {b : BasicWeight} (hb : b ≠ (0, 0)) {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) :
    p.shortNegativeSpan v = ⊤ := by
  exact p.shortNegativeSpan_eq_top_of_rootOperator_invariant v hv.1
    (NegativeCyclicity.RestrictedBridge.rootOperatorInvariant_eq_bot_or_top
      hU hhigh hb hv p)
    (p.isRootOperatorInvariant_shortNegativeSpan hv)

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
