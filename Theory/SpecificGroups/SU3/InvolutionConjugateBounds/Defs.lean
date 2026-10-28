module

public import BenderSuzuki.MatrixGroups.Unitary
public import Theory.GroupAction.PerfectCentralQuotient.ConjugateGeneration

/-!
# The concrete PSU₃ involution generation obligations

The actors are actual automorphisms of the projective special unitary matrix
group. Conjugators lie in that matrix group, so they lift through any given
central covering; allowing arbitrary conjugators from its full automorphism
group would not suffice for that application.

These predicates separate the two uniform five-conjugate branches above five
and the four-conjugate calculation at five. They assert no generation theorem.
Simplicity is inherited from the source component's specified quotient.

Source: Guralnick–Malle, *Classification of 2F-modules I*, §2 and
Proposition 4.3, manuscript pp.4 and 10–11, and its reference [13],
Guralnick–Saxl, *Generation of finite almost simple groups by conjugates*.
The uniform five-conjugate bound is an additional sufficient route;
Proposition 4.3 explicitly states that count at seven and four at five.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds
universe u

/-- The uniform estimate above five, restricted to inner involutory automorphisms. -/
def InnerFiveBound : Prop :=
  ∀ {E : Type u} [Field E] [Finite E] (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)] {p : ℕ},
    p.Prime → Odd p → 5 < p → Nat.card E = p ^ 2 →
    (∀ x, J.conj x = x ^ p) →
    ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J), a ≠ 1 → a ^ 2 = 1 →
    (∃ s, a = MulAut.conj s) → MulAut.HasInnerConjugateCover a 5

/-- The uniform estimate above five for every outer involution, with inner conjugators. -/
def OuterFiveBound : Prop :=
  ∀ {E : Type u} [Field E] [Finite E] (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)] {p : ℕ},
    p.Prime → Odd p → 5 < p → Nat.card E = p ^ 2 →
    (∀ x, J.conj x = x ^ p) →
    ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J), a ≠ 1 → a ^ 2 = 1 →
    (¬ ∃ s, a = MulAut.conj s) → MulAut.HasInnerConjugateCover a 5

/-- The stronger estimate at five, retaining both inner and outer involutions. -/
def FourBoundAtFive : Prop :=
  ∀ {E : Type u} [Field E] [Finite E] (J : HermitianForm 3 E)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)],
    Nat.card E = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J), a ≠ 1 → a ^ 2 = 1 →
    MulAut.HasInnerConjugateCover a 4

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds
