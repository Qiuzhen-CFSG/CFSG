module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.EightPointLine.Candidates
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.EightPointLine.Transport

/-!
# Independent obligations for the eight-point calculation

`NineCoverage` is exhaustive coverage of order-nine subgroups by the explicit
pairs of triples. `NineSieve` is the inner-normalizer calculation for a fixed
Sylow two-subgroup and those candidates that permute with it. These are
separate, unproved contracts here. Their conjunction, with the checked line
orders and Sylow conjugacy, suffices for the required invariant-line theorem.

Source: Aschbacher–Smith, proof of 1.3.4, printed p.511; GLS3, Table 5.3e.
The diagnostic in `source/check_candidates.py` is not a proof of either input.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint

/-- Uniform coverage on the actual alternating-group carrier. -/
def NineCoverage : Prop :=
  ∀ D : Subgroup Alt, Nat.card D = 9 → ∃ i : Fin 280, D = nineGroup i

/-- Only conjugation by elements of the fixed A₈ Sylow subgroup is tested. -/
def NineSieve : Prop :=
  ∀ i : Fin 280,
    (nineGroup i : Set Alt) * (twoGroup : Set Alt) =
      (twoGroup : Set Alt) * (nineGroup i : Set Alt) →
    ∀ g ∈ twoGroup ⊓ normalizer (nineGroup i : Set Alt),
      ∀ x ∈ nineLine i, g * x * g⁻¹ ∈ nineLine i

/-- Exhaustive coverage and the finite sieve solve the fixed-Sylow problem. -/
theorem fixedSylowLine_of_coverage_sieve (hcover : NineCoverage) (hsieve : NineSieve)
    (D : Subgroup Alt) (hcard : Nat.card D = 9)
    (hperm : (D : Set Alt) * (twoGroup : Set Alt) =
      (twoGroup : Set Alt) * (D : Set Alt)) : HasInvariantLine twoGroup D := by
  obtain ⟨i, rfl⟩ := hcover D hcard
  exact ⟨nineLine i, nineLine_le i, card_nineLine i, hsieve i hperm⟩

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint
end
