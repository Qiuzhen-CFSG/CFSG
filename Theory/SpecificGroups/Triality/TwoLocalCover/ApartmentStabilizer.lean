module

public import Theory.SpecificGroups.Triality.TwoLocalCover.Geometry
public import Theory.SpecificGroups.Triality.TwoLocalCover.ApartmentStabilizer.Opposition

/-!
# Oddness of the actual triality apartment fixer

The standard apartment is the normalizer orbit of both full-parabolic base
cosets. Its pointwise fixer therefore lies in the Borel and in its conjugate
by the concrete opposition representative. The matrix opposition calculation
bounds this intersection by the actual descended torus. Its proved order
(q³ − 1)(q − 1) is odd for every positive binary exponent.

No hexagon metric or cycle-conjugacy assertion enters this calculation.
It supplies the apartment-fixer input to the finite-building normalizer argument.

Sources: GLS3 2.3.4–5, 2.3.8(d), and §2.6, supporting Theorem 3.1.3
(`refs/KGroup/GLS3/chapter2.tex`, `chapter3.tex`).
-/

public section

namespace Triality.Standard.TwoLocalGeometry
open Subgroup Parabolics ConcreteBruhat

/-- Fixation of the normalizer translates of both base vertices places every
normalizer conjugate of an apartment fixer in the Borel. -/
theorem standardApartment_fixer_conjugate_mem_borel (f : ℕ) (hf : 0 < f)
    {x n : Carrier (binaryParameters f hf)}
    (hx : x ∈ fixingSubgroup (Carrier (binaryParameters f hf)) (standardApartment f hf))
    (hn : n ∈ normalizerCandidate (binaryParameters f hf) (binaryParameters_prime f hf)) :
    n⁻¹ * x * n ∈ borel (binaryParameters f hf) := by
  have hs (a : Node) : n⁻¹ * x * n ∈ parabolic (binaryParameters f hf) a := by
    rw [← CosetGeometry.stabilizer_base (parabolic (binaryParameters f hf)) a]
    apply MulAction.mem_stabilizer_iff.mpr
    have hfix := (mem_fixingSubgroup_iff _).mp hx _
      (show n • CosetGeometry.base (parabolic (binaryParameters f hf)) a ∈
        standardApartment f hf from ⟨n, hn, a, rfl⟩)
    simpa only [mul_smul, inv_smul_smul] using congrArg (n⁻¹ • ·) hfix
  rw [← parabolic_inf_binary (binaryParameters f hf) (binaryParameters_prime f hf)]
  exact ⟨hs _, hs _⟩

/-- The base and opposite chambers force the actual apartment fixer into the torus. -/
theorem standardApartment_fixer_le_torus (f : ℕ) (hf : 0 < f) :
    fixingSubgroup (Carrier (binaryParameters f hf)) (standardApartment f hf) ≤
      torus (binaryParameters f hf) := by
  intro x hx
  exact ApartmentStabilizer.borel_opposition_intersection f hf
    (standardApartment_fixer_le_borel f hf hx)
    (standardApartment_fixer_conjugate_mem_borel f hf hx
      (RelativeNormalizer.weylRepresentative_mem_normalizer _ (binaryParameters_prime f hf) (.r 3)))

/-- The pointwise fixer of the actual normalizer apartment has odd order,
for every positive binary exponent, including q = 2. -/
theorem standardApartment_fixer_odd (f : ℕ) (hf : 0 < f) :
    Odd (Nat.card (fixingSubgroup (Carrier (binaryParameters f hf)) (standardApartment f hf))) :=
  standardApartment_fixer_odd_of_le_torus f hf (standardApartment_fixer_le_torus f hf)

end Triality.Standard.TwoLocalGeometry
