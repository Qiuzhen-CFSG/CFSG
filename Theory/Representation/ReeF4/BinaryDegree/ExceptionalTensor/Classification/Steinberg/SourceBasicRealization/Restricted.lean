module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization.BasicFactors
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceHighestWeight
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism

/-!
# Realizing every restricted algebraic highest weight

Expand a source restricted weight into exceptional binary digits, realize
each of the four basic digits by the concrete source factors, and apply the
proved algebraic tensor theorem. The actual highest-weight uniqueness and
the actual exceptional algebraic morphism discharge its representation and
endomorphism inputs.

The sole remaining geometric premise is universality of the literal F4
carrier, retained with its existing algebraic-realization producer. This
does not assert irreducibility or exhaustion after finite restriction.

Source: GLS3 Theorem 2.8.5; Steinberg (1963), Theorem 5.1 and Section 11.
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- The basic-existence premise in the actual restricted algebraic realization
is discharged; only genuine universality of the carrier is retained. -/
theorem exists_restricted_algebraicFactor
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    {k : ℕ} (a : Weight) (ha : InRestrictedRange (2 * k + 1) a) :
    ∃ A : AlgebraicFactor F, HasHighestWeight A a := by
  classical
  obtain ⟨b, hb⟩ := exists_tensorWeight a ha
  choose B hB using fun i : ZMod (2 * k + 1) =>
    exists_basic_algebraicFactor (F := F) (b i)
  obtain ⟨A, hA, _⟩ := AlgebraicTensor.exists_pointTensor_factor hU
    SourceHighestWeight.equivalent_of_same_highestWeight
    (Geometry.ExceptionalMorphism.morphism (F := F))
    (Geometry.ExceptionalMorphism.morphism_bijective (F := F)).surjective
    Geometry.ExceptionalMorphism.morphism_rootFormula B b hB
  exact ⟨A, hb ▸ hA⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization

