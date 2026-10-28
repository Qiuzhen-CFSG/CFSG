module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.PositivePrimitives.WeightNilpotence
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.PositivePrimitives.Pairing
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.PositivePrimitives.ContravariantForm

/-!
# Positive short-root primitives

Negative short-root cyclicity from a genuine highest vector implies uniform
nilpotence of the positive short-root coefficient action, by the finite range
of integral coroot weights. A nondegenerate contravariant pairing then
identifies its common kernel with the highest-vector line.

In characteristic two, highest-weight uniqueness constructs this pairing from
the actual rational dual and the Weyl representative of root negation. Thus
both conclusions hold for a nonzero basic highest weight, with negative
short-root cyclicity and the raw highest-weight uniqueness contract as the
only additional hypotheses. The separate pairing-based reduction is preserved.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §§2.7–2.9, 4.3–4.5 and 11.1(1),(3),
DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
variable {F : Type*} [Field F] [IsAlgClosed F]

/-- The two positive-action conclusions follow from negative cyclicity and an
actual nondegenerate contravariant pairing. Pairing existence remains explicit. -/
theorem RootExpansion.positivePrimitives_of_contravariantPairing
    {B : AlgebraicFactor F} (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) (hspan : p.shortNegativeSpan v = ⊤)
    (hpair : p.HasShortContravariantPairing) :
    p.shortPositiveKernel = Submodule.span F {v} ∧ p.HasNilpotentShortPositiveAction :=
  ⟨p.shortPositiveKernel_eq_span_of_contravariantPairing hv hspan hpair,
    p.hasNilpotentShortPositiveAction_of_negative_span hv hspan⟩

/-- For a nonzero basic weight, the common positive short-root kernel is the
highest-vector line. The contravariant pairing is constructed from rational
duality and highest-weight uniqueness, with negative cyclicity explicit. -/
theorem RootExpansion.shortPositiveKernel_eq_span_of_negative_span
    [CharP F 2]
    (hhigh : ∀ (A C : AlgebraicFactor F) (a : Weight),
      HasHighestWeight A a → HasHighestWeight C a →
        AreEquivalentRepresentations A.action C.action)
    {B : AlgebraicFactor F} (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hb : b ≠ (0, 0)) (hv : B.IsBasicHighestWeightVector b v)
    (hspan : p.shortNegativeSpan v = ⊤) :
    p.shortPositiveKernel = Submodule.span F {v} :=
  p.shortPositiveKernel_eq_span_of_contravariantPairing hv hspan
    (p.hasShortContravariantPairing_of_negative_span hhigh hb hv hspan)

/-- Negative short-root cyclicity for a nonzero basic highest vector gives
both the unique positive primitive line and uniform positive-word nilpotence.
Only the raw highest-weight uniqueness contract is additionally needed. -/
theorem RootExpansion.positivePrimitives_of_negative_span
    [CharP F 2]
    (hhigh : ∀ (A C : AlgebraicFactor F) (a : Weight),
      HasHighestWeight A a → HasHighestWeight C a →
        AreEquivalentRepresentations A.action C.action)
    {B : AlgebraicFactor F} (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hb : b ≠ (0, 0)) (hv : B.IsBasicHighestWeightVector b v)
    (hspan : p.shortNegativeSpan v = ⊤) :
    p.shortPositiveKernel = Submodule.span F {v} ∧ p.HasNilpotentShortPositiveAction :=
  ⟨p.shortPositiveKernel_eq_span_of_negative_span hhigh hb hv hspan,
    p.hasNilpotentShortPositiveAction_of_negative_span hv hspan⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
