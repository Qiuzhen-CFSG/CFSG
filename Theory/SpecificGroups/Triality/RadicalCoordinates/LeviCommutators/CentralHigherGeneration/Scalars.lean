module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.RootArithmetic
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Pairing
/-!
# Scalar generation for the third short triality root

The coefficient b(s,t) = s F(t) + F(s) t is the leading coefficient of the
exchange between the first two short root orbits. Every trace-zero v equals
b(1,F(v)). A nontrivial Frobenius orbit supplies t for which
F(t) + F²(t) is nonzero; the trace pairing then makes Tr(b(s,t)) arbitrary.
Subtracting one such value reduces any scalar to the trace-zero case.
Thus two b-values suffice, including over the binary base field.

Source: the folded G₂ relation in GLS3 2.4.5(b)(4), with the marking fixed by
`FoldedRoots.lean`; used in Aschbacher–Smith F.1.12(II), pp.263–264.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.RadicalCoordinates.LeviCommutators
open Centers

/-- The position-7 coefficient in the exchange of short orbits 0 and 1. -/
def higherCoefficient (P : Parameters) (s t : ExtensionField P) : ExtensionField P :=
  s * fieldFrobenius P t + fieldFrobenius P s * t

theorem trace_higherCoefficient (P : Parameters) (s t : ExtensionField P) :
    cubicTrace P (higherCoefficient P s t) =
      cubicTrace P (s * (fieldFrobenius P t + fieldFrobenius P (fieldFrobenius P t))) := by
  apply Subtype.ext
  simp only [cubicTrace_coe, higherCoefficient, map_add, Subfield.coe_add, map_mul, fieldFrobenius_three]
  ring

theorem higherCoefficient_trace_zero (P : Parameters) (hp : P.prime = 2)
    (v : ExtensionField P) (hv : cubicTrace P v = 0) :
    higherCoefficient P 1 (fieldFrobenius P v) = v := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have h : v + (fieldFrobenius P v + fieldFrobenius P (fieldFrobenius P v)) = 0 := by
    simpa only [cubicTrace_coe, Subfield.coe_zero, add_assoc] using congrArg Subtype.val hv
  simpa only [higherCoefficient, map_one, one_mul, add_comm] using
    (CharTwo.add_eq_zero.mp h).symm

/-- Two leading exchange coefficients additively generate every cubic scalar. -/
theorem exists_sum_higherCoefficient (P : Parameters) (hp : P.prime = 2)
    (v : ExtensionField P) :
    ∃ s t u : ExtensionField P,
      v = higherCoefficient P s t + higherCoefficient P 1 u := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  obtain ⟨t, ht⟩ := ElementaryCentralKernel.exists_frobenius_moved P
  let d := fieldFrobenius P t + fieldFrobenius P (fieldFrobenius P t)
  have hd : d ≠ 0 := by
    intro h
    have he := CharTwo.add_eq_zero.mp h
    exact ht ((fieldFrobenius P).injective he).symm
  let s := (cubicTrace P v).val * d⁻¹
  have hs : cubicTrace P (higherCoefficient P s t) = cubicTrace P v := by
    rw [trace_higherCoefficient]
    change cubicTrace P (s * d) = _
    simp only [s, mul_assoc, inv_mul_cancel₀ hd, mul_one, cubicTrace_fixed P hp]
  have hz : cubicTrace P (v + higherCoefficient P s t) = 0 := by
    rw [map_add, hs]
    apply Subtype.ext
    simp only [Subfield.coe_zero, CharTwo.add_self_eq_zero]
  refine ⟨s, t, fieldFrobenius P (v + higherCoefficient P s t), ?_⟩
  rw [higherCoefficient_trace_zero P hp _ hz, add_left_comm,
    CharTwo.add_self_eq_zero, add_zero]

end Triality.Standard.RadicalCoordinates.LeviCommutators
