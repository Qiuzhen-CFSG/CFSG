module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.ProjectiveData
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation.RestrictedRelations
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation.RootNormalization
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation.QuotientKernel
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation.HighestLine

/-!
# Conjugation data for the actual simple differential quotient

The implementer is constructed by descending actual conjugation through the
surjective quotient action and using innerness of endomorphism-algebra
automorphisms. The canonical representation differential proves root-algebra
normalization. Connectedness fixes the finite orbit of the simple quotient's
annihilator, so the quotient is equivalent to each conjugation twist. Finally,
triangular spanning and joint negative nilpotence give Curtis's full
positive-root primitive line on this quotient.

`SimpleCyclicQuotient.nonempty_conjugationData` combines these results and
discharges all three premises of the conditional assembly. It retains only the
universal-version hypothesis used for connectedness and the original basic
highest-vector hypothesis; the basic weight may also be zero.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), Curtis 2.7 and equations 4.1–4.2; DOI 10.1017/S0027763000011016.
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

namespace SimpleCyclicQuotient
variable {B : AlgebraicFactor F} {v : B.Space} (Q : SimpleCyclicQuotient B v)

/-- Assemble the data from normalization, kernel stability, and the primitive line. -/
theorem conjugationData_of_kernel (hs : RootConjugationStable B)
    (hk : ∀ (g : PointGroup F) (a : rootAlgebra B),
      Q.rootAction (rootConjugate B hs g a) = 0 ↔ Q.rootAction a = 0)
    (hp : ∀ w : Q.Space,
      (∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r → Q.operator r w = 0) →
        w ∈ Submodule.span F {Q.highestVector}) : Nonempty Q.ConjugationData := by
  exact ⟨{ conjugate := rootConjugate B hs
           conjugate_eq := rootConjugate_eq B hs
           implementer := fun g => Q.implementer_of_kernel (rootConjugate B hs g) (hk g)
           primitive_line := hp }⟩

/-- Curtis's conjugation and full positive-root highest-line data for the
actual simple differential quotient. The universal-version hypothesis supplies
connectedness for kernel stability; all other auxiliary premises are discharged. -/
theorem nonempty_conjugationData [CharP F 2]
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    {b : BasicWeight} (hv : B.IsBasicHighestWeightVector b v) :
    Nonempty Q.ConjugationData :=
  Q.conjugationData_of_kernel (rootConjugationStable B)
    (Q.rootAction_rootConjugate_eq_zero_iff hU (rootConjugationStable B))
    (Q.primitive_line hv)

end SimpleCyclicQuotient
end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
