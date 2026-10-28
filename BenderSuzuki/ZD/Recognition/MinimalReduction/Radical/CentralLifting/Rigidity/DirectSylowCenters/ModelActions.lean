module

public import BenderSuzuki.SE.Models
public import Theory.GroupTheory.PerfectCentralCoverSylowCenterCriterion

/-!
# The two remaining concrete action contracts for direct cover rigidity

Each contract concerns an actual Sylow subgroup of a specified matrix group,
its actual normalizer, and binary homomorphisms on that Sylow. Neither is an
assumption about the covering group or its center. The generic criterion
transports one such Sylow through the original model isomorphism and cover.

The Suzuki contract retains m ≥ 1, including Sz(8). The unitary contract
retains n ≥ 2, the coefficient field, Hermitian form and fixed-field size.
Simplicity may be inherited from the given simple Bender group.

These are explicit, not yet discharged inputs to the alternative proof of
GLS4, Chapter 4, Lemma 2.8(c).
-/

namespace BenderSuzuki.ZD.DirectSylowCenters
open _root_.BenderSuzuki.MatrixGroups PerfectCentralCovering

/-- Concrete Suzuki normalizer action data, at every admissible parameter. -/
@[expose] public def SuzukiCenterActions : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ Q : Sylow 2 (SuzukiMatrixGroup m),
    SylowCenterAction (Q : Subgroup (SuzukiMatrixGroup m))

/-- Concrete unitary normalizer action data with the original model guards. -/
@[expose] public def UnitaryCenterActions : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (J : HermitianForm 3 K)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (n : ℕ), 2 ≤ n → J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] →
    Nat.card K = (2 ^ n) ^ 2 → Nat.card {x : K // J.conj x = x} = 2 ^ n →
    ∃ Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      SylowCenterAction (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))

end BenderSuzuki.ZD.DirectSylowCenters
