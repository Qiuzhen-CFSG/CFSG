module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Alternatives
public import BenderSuzuki.MatrixGroups.Suzuki

/-!
# The two preliminary targets for the maximal-prime closure argument

The prime bound concerns every solvable overgroup of the original H inside
Mc. The Suzuki exclusion concerns the actual image of each relative
C-component in Mc/O₂(Mc), not an unrelated model tag or intrinsic quotient.
These predicates are obligations, not assertions that the source hypotheses
already imply them. They are shared by the independent prime/Suzuki and
nonnormal-model branches of 14.6.14.

Source: Aschbacher--Smith, first two paragraphs of the proof of 14.6.14,
printed pp.1032--1033.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
variable {G : Type*} [Group G]

/-- The prime support of every literal solvable overgroup H⁺ of H in Mc. -/
def SolvableOvergroupPrimeBound (H Mc : Subgroup G) (p : ℕ) : Prop :=
  ∀ J : Subgroup G, H ≤ J → J ≤ Mc → Group.IsSolvable J →
    ∀ q : ℕ, q.Prime → q ∣ Nat.card J → q = 2 ∨ q = 3 ∨ (p = 5 ∧ q = 5)

/-- No actual relative component image is Sz(2^(2m+1)), for m > 0. -/
def NoSuzukiComponents (Mc : Subgroup G) : Prop :=
  ∀ J : Subgroup G, J ≤ Mc → (J.subgroupOf Mc).IsCComponent →
    ∀ m : ℕ, 0 < m →
      ¬ Nonempty (((J.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
