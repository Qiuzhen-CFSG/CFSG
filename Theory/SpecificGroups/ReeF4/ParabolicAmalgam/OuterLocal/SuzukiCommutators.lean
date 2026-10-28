module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.RootCurve
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.TorusScaling
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Suzuki-side radical commutators from the fixed end-root curve

For the concrete additive root curve `x`, a scalar conjugation
`h * x(t) * h⁻¹ = x(c*t)` gives `[h,x(t)] = x((c-1)*t)`. If `c ≠ 1`, every
curve element lies in the derived subgroup. Normal generation of the radical
by this curve then puts the whole radical in the derived subgroup, since
that subgroup is normal inside the seed.

The curve, its fixedness, radical membership and additive law are proved
from the root matrices in `RootCurve`. `NormalGeneration` proves normal
generation of the actual fixed radical, and `TorusScaling` constructs the
scalar actor inside the fixed Suzuki seed. For the canonical local input
and `m ≥ 1`, `radical_le_commutator` combines these results with every
root-calculation premise discharged. It requires no quotient projection
or perfectness hypothesis.

Source: the radical contribution to Aschbacher–Smith F.1.12(II)(i), printed
pp.263–264 (PDF pp.274–275) of `refs/quasithin.pdf`. The existing `Residual`
module lifts the inclusion through the perfect Suzuki quotient. The intended
application has `m ≥ 1`; no nonidentity scalar actor is asserted at `m = 0`.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.OuterLocal.SuzukiCommutators

open LargeLocalSeeds
open scoped commutatorElement

/-- A scalar conjugation evaluates the commutator on the actual fixed root curve. -/
theorem endRootElement_commutator_of_scaling {m : ℕ} (d : LocalBlockInput m)
    (h : standardSeed d .suzuki) (c : CoefficientField m)
    (hscale : ∀ t, h * endRootElement d t * h⁻¹ = endRootElement d (c * t))
    (t : CoefficientField m) :
    ⁅h, endRootElement d t⁆ = endRootElement d ((c - 1) * t) := by
  rw [commutatorElement_def, hscale, ← endRootElement_neg, ← endRootElement_add]
  congr 1
  ring

/-- A nonidentity scalar makes every parameter a commutator parameter. -/
theorem endRootElement_mem_commutator_of_scaling {m : ℕ} (d : LocalBlockInput m)
    (h : standardSeed d .suzuki) (c : CoefficientField m) (hc : c ≠ 1)
    (hscale : ∀ t, h * endRootElement d t * h⁻¹ = endRootElement d (c * t))
    (t : CoefficientField m) : endRootElement d t ∈ commutator (standardSeed d .suzuki) := by
  have he : ⁅h, endRootElement d ((c - 1)⁻¹ * t)⁆ = endRootElement d t := by
    rw [endRootElement_commutator_of_scaling d h c hscale, ← mul_assoc,
      mul_inv_cancel₀ (sub_ne_zero.mpr hc), one_mul]
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- Conditional assembly: normal generation by the end-root curve and a
nontrivial scalar action place the whole radical in the seed's derived subgroup.
The canonical seed's two premises are discharged in `radical_le_commutator`. -/
theorem radical_le_commutator_of_normal_generation_and_scaling {m : ℕ}
    (d : LocalBlockInput m)
    (hgen : seedRadical d .suzuki ≤ Subgroup.normalClosure (Set.range (endRootElement d)))
    (h : standardSeed d .suzuki) (c : CoefficientField m) (hc : c ≠ 1)
    (hscale : ∀ t, h * endRootElement d t * h⁻¹ = endRootElement d (c * t)) :
    seedRadical d .suzuki ≤ commutator (standardSeed d .suzuki) := by
  apply hgen.trans
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨t, rfl⟩
  exact endRootElement_mem_commutator_of_scaling d h c hc hscale t

/-- For `m ≥ 1`, the actual root-defined Suzuki radical lies in the derived
subgroup of the canonical fixed seed. Normal generation and the nontrivial
scalar action are both proved from the concrete root matrices. -/
theorem radical_le_commutator {m : ℕ} (hm : 1 ≤ m) :
    seedRadical (canonicalLocalBlockInput m) .suzuki ≤
      commutator (standardSeed (canonicalLocalBlockInput m) .suzuki) := by
  obtain ⟨h, c, hc, hscale⟩ := exists_endRootElement_scaling hm
  exact radical_le_commutator_of_normal_generation_and_scaling
    (canonicalLocalBlockInput m) (NormalGeneration.radical_le_normalClosure hm)
    h c hc hscale

end ReeF4.Parabolics.OuterLocal.SuzukiCommutators
