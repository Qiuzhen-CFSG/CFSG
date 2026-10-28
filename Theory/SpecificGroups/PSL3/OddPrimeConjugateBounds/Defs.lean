module

public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.NormalForm
public import Theory.GroupAction.PerfectCentralQuotient.ConjugateGeneration

/-!+# The two odd-prime PSL₃ involution generation obligations

These predicates separate inner involutions from linear-times-graph
involutions. Every conjugator belongs to the actual projective matrix group,
which is essential for lifting the conjugators to an arbitrary central cover.
The checked automorphism normal form exhausts the two branches. These are
contracts for model calculations, not assertions that those calculations hold.

Source: Guralnick–Malle, *Classification of 2F-modules I*, (2.6) and
Proposition 4.2, manuscript pp.4 and 9–10; Aschbacher–Smith K.2, p.453.
Proposition 4.2 explicitly uses three conjugates at p = 3. The uniform
odd-prime generation bound is the sufficient route requested for K.2.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.OddPrimeConjugateBounds
open OuterSolvable
universe u

/-- Three inner conjugates suffice for each nonidentity inner involution. -/
def InnerThreeBound : Prop :=
  ∀ {F : Type u} [Field F] [Finite F] [IsSimpleGroup PSL(3,F)],
    (¬ Group.IsSolvable PSL(3,F)) →
    ∀ {p : ℕ}, p.Prime → Odd p → Nat.card F = p →
    ∀ a : MulAut PSL(3,F), a ≠ 1 → a ^ 2 = 1 →
      a ∈ MulAut.innerSubgroup PSL(3,F) → MulAut.HasInnerConjugateCover a 3

/-- Three inner conjugates suffice for each nonidentity linear-times-graph involution. -/
def GraphThreeBound : Prop :=
  ∀ {F : Type u} [Field F] [Finite F] [IsSimpleGroup PSL(3,F)],
    (¬ Group.IsSolvable PSL(3,F)) →
    ∀ {p : ℕ}, p.Prime → Odd p → Nat.card F = p →
    ∀ g : GL (Fin 3) F,
      linearConj F g * graph F ≠ 1 → (linearConj F g * graph F) ^ 2 = 1 →
      MulAut.HasInnerConjugateCover (linearConj F g * graph F) 3

/-- The checked normal form reduces the full model estimate to two independent calculations. -/
theorem three_bound_of_inner_graph
    (hi : InnerThreeBound.{u}) (hg : GraphThreeBound.{u})
    {F : Type u} [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]
    (hns : ¬ Group.IsSolvable PSL(3,F)) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (a : MulAut PSL(3,F)) (ha : a ≠ 1) (ha2 : a ^ 2 = 1) :
    MulAut.HasInnerConjugateCover a 3 := by
  obtain ⟨g, he | he⟩ := OddInvolutionFixed.automorphism_normal_form hns hp ho hF a
  · subst a
    exact hi hns hp ho hF _ ha ha2
      (OddInvolutionFixed.linearConj_involution_inner g ha2)
  · subst a
    exact hg hns hp ho hF g ha ha2

end Matrix.PSL3.OddPrimeConjugateBounds
