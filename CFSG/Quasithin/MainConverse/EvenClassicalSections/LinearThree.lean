module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Reduction

/-!
# Proper simple sections of PSL₃ over even fields

The full point and line parabolic section calculations are proved, and the
linear subfield induction is assembled with explicit remaining inputs in
`LinearThree.Reduction`. The intrinsic proper-subgroup exhaustion and the
unitary subfield section theorem are still required. No unconditional
PSL₃(2^f) proper-K theorem is asserted here for f ≥ 2.

Source: Aschbacher–Smith, Main Hypothesis 0.1.1(K) and Theorem 0.1.2(1),
printed pp.4 and 482; Hartley–Mitchell, GLS3, Theorem 6.5.3.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple LinearThreeSections
open scoped MatrixGroups

/-- Conditional proper-K assembly. Both remaining mathematical inputs must be
discharged before this becomes the source converse's K clause. -/
public theorem psl3_even_properK_of_exhaustion
    (hexhaustion : ∀ f, 2 ≤ f → ∀ (F : Type) [Field F] [Finite F],
      Nat.card F = 2 ^ f → ∀ U : Subgroup PSL(3, F), U ≠ ⊤ → Envelope f U)
    (hunitary : ∀ m, 0 < m → ∀ (L : Type) [Group L],
      ClassicalGroup.IsPSU L 3 (2 ^ m) → IsKGroup IsConstructedCarrier L)
    {G : Type*} [Group G] {f : ℕ} (hf : 0 < f)
    (hG : ClassicalGroup.IsPSL G 3 (2 ^ f)) :
    HasProperKSubgroups IsConstructedCarrier G :=
  (psl3_isKGroup_of_exhaustion hexhaustion hunitary hf hG).properK

/-- The simple target may inhabit a different universe from its numerator. -/
public theorem psl3_even_simpleSection_of_exhaustion
    (hexhaustion : ∀ f, 2 ≤ f → ∀ (F : Type) [Field F] [Finite F],
      Nat.card F = 2 ^ f → ∀ U : Subgroup PSL(3, F), U ≠ ⊤ → Envelope f U)
    (hunitary : ∀ m, 0 < m → ∀ (L : Type) [Group L],
      ClassicalGroup.IsPSU L 3 (2 ^ m) → IsKGroup IsConstructedCarrier L)
    {G : Type*} [Group G] {f : ℕ} (hf : 0 < f)
    (hG : ClassicalGroup.IsPSL G 3 (2 ^ f))
    (U : Subgroup G) (hU : U ≠ ⊤) (V : Subgroup U)
    {S : Type*} [Group S] [IsSimpleGroup S]
    (p : V →* S) (hp : Function.Surjective p) : IsConstructedCarrier S :=
  SymmetricEight.constructed_section_of_isKGroup
    (psl3_even_properK_of_exhaustion hexhaustion hunitary hf hG U hU) V p hp

/-- Normality is relative to the subgroup V, as required for a section. -/
public theorem psl3_even_simpleQuotient_of_exhaustion
    (hexhaustion : ∀ f, 2 ≤ f → ∀ (F : Type) [Field F] [Finite F],
      Nat.card F = 2 ^ f → ∀ U : Subgroup PSL(3, F), U ≠ ⊤ → Envelope f U)
    (hunitary : ∀ m, 0 < m → ∀ (L : Type) [Group L],
      ClassicalGroup.IsPSU L 3 (2 ^ m) → IsKGroup IsConstructedCarrier L)
    {G : Type*} [Group G] {f : ℕ} (hf : 0 < f)
    (hG : ClassicalGroup.IsPSL G 3 (2 ^ f))
    (U : Subgroup G) (hU : U ≠ ⊤) (V : Subgroup U)
    (N : Subgroup V) [N.Normal] [IsSimpleGroup (V ⧸ N)] :
    IsConstructedCarrier (V ⧸ N) :=
  psl3_even_simpleSection_of_exhaustion hexhaustion hunitary hf hG U hU V
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end CFSG.Quasithin.MainConverse
