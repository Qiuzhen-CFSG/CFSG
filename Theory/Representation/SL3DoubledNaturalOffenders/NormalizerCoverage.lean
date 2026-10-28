module

public import Theory.Representation.SL3DoubledNaturalOffenders.NormalizerCoverage.Semilinear
public import Theory.Representation.SL3DoubledNaturalOffenders.NormalizerCoverage.Factorization
public import Theory.Representation.SL3DoubledNaturalOffenders.NormalizerCoverage.TensorInvolutions

/-!
# Involution coverage for the doubled natural SL₃ normalizer

The center of the full multiplicity commutant recovers the original field.
Consequently every involution of the literal binary normalizer is field linear
when the field has odd binary degree, including degree one. The intertwining
blocks then yield invertible natural and multiplicity factors. Their reciprocal
scalar squares allow a reciprocal rescaling into SL₃ and SL₂ without changing
the action. Thus each normalizer involution belongs to the literal tensor
subgroup, as does every elementary two-subgroup of the normalizer.

This discharges tensor containment for the doubled-natural offender estimate.
The further exclusion of nontrivial multiplicity action is a separate step in
the source offender localization. Oddness already implies positive field degree.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), B.5.9(3) and B.5.10(2), printed pp.107–109.
-/

public section

namespace Representation.SL3DoubledNaturalOffenders

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- Every square-one element of the marked binary normalizer over an odd-degree
binary field lies in the actual SL₃ × SL₂ tensor subgroup, including over `F₂`. -/
theorem normalizer_involution_mem_tensorSubgroup {m : ℕ} (hodd : Odd m)
    (hc : Nat.card F = 2 ^ m) (b : Ambient F) (hb : b ∈ normalizer F)
    (hb2 : b ^ 2 = 1) : b ∈ tensorSubgroup F := by
  obtain ⟨g, c, hfactors⟩ := normalizer_involution_tensor_factors hodd hc b hb hb2
  exact involution_mem_tensorSubgroup_of_gl_factors b g c hfactors hb2

/-- An elementary two-subgroup of the marked normalizer satisfies the tensor
containment premise of the doubled-natural offender estimate. -/
theorem normalizer_elementary_le_tensorSubgroup {m : ℕ} (hodd : Odd m)
    (hc : Nat.card F = 2 ^ m) (A : Subgroup (Ambient F))
    (hA : BinaryOffender.IsElementaryTwo A) (hAN : A ≤ normalizer F) :
    A ≤ tensorSubgroup F := by
  let : IsElementaryAbelian 2 A := hA.2
  intro a ha
  exact normalizer_involution_mem_tensorSubgroup hodd hc a (hAN ha)
    (elemPow_eq_one_of_isElementaryAbelian a ha)

end Representation.SL3DoubledNaturalOffenders
