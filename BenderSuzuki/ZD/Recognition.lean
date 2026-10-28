module

public import BenderSuzuki.ZD.Recognition.Simple

/-!
# Assembly of the product-disconnected recognition theorem

Theorem ZD is proved by strong induction on the group order. The source
reduces a minimal counterexample to the simple case (GLS, Volume 4, Chapter 2,
Sections 3–4), proves strong embedding in the residual case (Sections 5–17),
and uses Bender--Suzuki recognition. The simple strongly embedded case is
proved in `Recognition.Simple`. This module implements strong induction and
assembles that proof with the two remaining mathematical reductions, which
remain explicit inputs until their proofs are supplied.
-/

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFchapter1section1

universe u

/-- A minimal counterexample is in the rank-at-least-two branch. -/
public theorem MinimalCounterexample.rank_at_least_two
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) : TwoRankAtLeastTwo (Subgroup.closure Z) := by
  by_contra hrank
  exact h.fails (Or.inl hrank)

/-- Strong induction on cardinality reduces Theorem ZD to exclusion of a
minimal counterexample. The universal premise includes quotients. -/
public theorem conclusion_of_no_minimalCounterexample
    (exclude : ∀ {G : Type u} [Group G] [Finite G]
      (Z : Set G) (M : Subgroup G), MinimalCounterexample Z M → False)
    {G : Type u} [Group G] [Finite G]
    (Z : Set G) (M : Subgroup G) (h : IsProductDisconnected Z M) :
    Conclusion Z M := by
  have main : ∀ n : ℕ, ∀ {H : Type u} [Group H] [Finite H],
      Nat.card H = n → ∀ (W : Set H) (N : Subgroup H),
        IsProductDisconnected W N → Conclusion W N := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H _ _ hcard W N hWN
      by_contra hfail
      apply exclude W N
      refine ⟨hWN, hfail, ?_⟩
      intro K _ _ hK U P hUP
      exact ih (Nat.card K) (hcard ▸ hK) rfl U P hUP
  exact main (Nat.card G) rfl Z M h

/-- Assemble the minimal-counterexample reduction, residual strong embedding,
and the simple strongly embedded recognition bridge. Every input is a
mathematical obligation; none is installed as an axiom or instance. -/
public theorem conclusion_of_reductions
    (reduce : ∀ {G : Type u} [Group G] [Finite G]
      (Z : Set G) (M : Subgroup G),
      MinimalCounterexample Z M → SimpleReduction Z M)
    (embed : ∀ {G : Type u} [Group G] [Finite G]
      (Z : Set G) (M : Subgroup G),
      MinimalCounterexample Z M → SimpleReduction Z M → IsStronglyEmbedded M)
    (recognize : ∀ {G : Type u} [Group G] [Finite G]
      (Z : Set G) (M : Subgroup G),
      IsProductDisconnected Z M → IsSimpleGroup G → IsStronglyEmbedded M →
      Conclusion Z M)
    {G : Type u} [Group G] [Finite G]
    (Z : Set G) (M : Subgroup G) (h : IsProductDisconnected Z M) :
    Conclusion Z M := by
  apply conclusion_of_no_minimalCounterexample (Z := Z) (M := M) _ h
  intro H _ _ W N hmin
  have hsimple := reduce W N hmin
  exact hmin.fails
    (recognize W N hmin.disconnected hsimple.simple (embed W N hmin hsimple))

/-- Strong induction and the checked Theorem SE bridge reduce ZD to the two
outstanding source arguments: the simple reduction and residual strong
embedding. This is conditional assembly, not the unconditional Theorem ZD. -/
public theorem conclusion_of_simple_and_embedding_reductions
    (reduce : ∀ {G : Type u} [Group G] [Finite G]
      (Z : Set G) (M : Subgroup G),
      MinimalCounterexample Z M → SimpleReduction Z M)
    (embed : ∀ {G : Type u} [Group G] [Finite G]
      (Z : Set G) (M : Subgroup G),
      MinimalCounterexample Z M → SimpleReduction Z M → IsStronglyEmbedded M)
    {G : Type u} [Group G] [Finite G]
    (Z : Set G) (M : Subgroup G) (h : IsProductDisconnected Z M) :
    Conclusion Z M := by
  apply conclusion_of_reductions reduce embed _ Z M h
  intro H _ _ W N hWN hsimple hN
  exact Or.inr (structure_of_simple_stronglyEmbedded W N hWN hsimple hN)

end BenderSuzuki.ZD
