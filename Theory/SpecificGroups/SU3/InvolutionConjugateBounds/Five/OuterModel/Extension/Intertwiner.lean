module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.Setup

/-!
# A projective Frobenius normalizer for the alternating subgroup

The remaining matrix calculation seeks a unitary matrix whose Frobenius
twist implements any odd permutation on an actual embedded A₇.
No order, marking, or scalar-norm condition is an input. The embedding may
be changed. The extension proof corrects the odd permutation by an even one
before constructing its involution and normalizing its action.

This is an explicit, unproved matrix input. `OuterModel.Extension` constructs
the faithful S₇ action and its literal entrywise marking from this input.
Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11.
-/

@[expose] public noncomputable section
open Equiv
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer

/-- Conjugation by the specified triple transposition on the alternating group. -/
def tripleSwapAction : MulAut (alternatingGroup (Fin 7)) :=
  MulAut.conjNormal tripleSwap

/-- A matrix intertwining equation, with the given A₇ existence hypothesis
retained. The action is on the projective image, retaining scalar ambiguity. -/
def ProjectiveOddNormalizer : Prop :=
  ∀ [IsSimpleGroup ConcreteGroup],
    (∃ j : alternatingGroup (Fin 7) →* ConcreteGroup, Function.Injective j) →
    ∃ (j : alternatingGroup (Fin 7) →* ConcreteGroup) (u : concreteForm.unitarySubgroup)
      (r : Perm (Fin 7)),
      Function.Injective j ∧ r ∉ alternatingGroup (Fin 7) ∧
      ∀ q, (concreteForm.unitaryConj u * concreteActor) (j q) = j ((MulAut.conjNormal r) q)

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer
