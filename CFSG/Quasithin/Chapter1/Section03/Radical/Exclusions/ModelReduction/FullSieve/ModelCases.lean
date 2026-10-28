module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Quotients
public import Theory.AtlasPort.LinearGroups.G2.Basic

/-!
# The model information consumed by the radical sieve

This is a projection to be proved from the full conclusion of C.2.7,
not an alternative statement of that lemma or an authorized source premise.
In particular it omits the stabilizer and offender clauses. The source
adapter must formulate the entire lemma before deriving this projection.

Block types retain their actual core quotient and conjugation module.
For the two non-block alternatives, the model belongs to the actual star
image instead. The G₂(2) case uses the derived group, as in C.1.30.
These distinctions allow the group comparisons to proceed independently
of the full pushing-up source interface.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
C.1.30, printed p.135; C.2.7(3), pp.145–147; proof of 1.3.8, p.514.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve

open Subgroup
variable {G : Type*} [Group G]

/-- The full special-linear group over a nontrivial binary field.
The center is not divided out in this model. -/
def IsSLThreeEven (Q : Type*) [Group Q] : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
    Nat.card F = 2 ^ n ∧ Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 3) F)

/-- Only the model information needed from C.2.7. Every constructor must
be obtained from the corresponding full source alternative, including its
module/action and stabilizer clauses. This is not a source-theorem input. -/
inductive ModelCases (H₀ K R : Subgroup G) : Prop
  | binary (block : ChapterC.IsBlock (K.subgroupOf H₀))
      (model : ∃ n, ChapterC.IsL2EvenBlock K n)
  | alternating (n : ℕ) (lower : 5 ≤ n) (upper : n ≤ 8)
      (block : ChapterC.IsBlock (K.subgroupOf H₀))
      (model : ChapterC.IsAlternatingBlock K n)
  | ahatSix (model : ChapterC.IsExceptionalAhat6Block K)
  | exceptionalSeven (model : ChapterC.IsExceptionalA7Block K)
  | symplecticFour (model : ChapterC.IsSp4FourBlock K)
  | binaryG2 (model : Nonempty
      (XiQuotient K ≃* commutator (Atlas.G2.Model (ZMod 2))))
  | linearThree (model : IsSLThreeEven (starImage K R K))
  | binaryLinear (n : ℕ) (degree : n = 4 ∨ n = 5)
      (model : ClassicalGroup.IsPSL (starImage K R K) n 2)

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve
