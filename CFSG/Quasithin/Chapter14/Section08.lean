module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Choosing the local subgroup for Theorem D

Theorem D is Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 14.8.2 (combined 1 March 2004 manuscript, printed pp. 1078–1079).
Its reduction to Hypothesis 13.3.1 requires choosing a member `L` of the
nonempty family `Lf(G,T)` so that, if `L/O₂(L)` is `A₅`, every member has
that quotient. The selection lemma below proves this for any nonempty
family of subgroups, using actual quotient groups and multiplicative
equivalences with the alternating group on five letters.

Choose a member whose quotient is not `A₅` if one exists; otherwise any
member works. Unlike the printed choice of a maximal member, this choice
needs no descent along inclusions: Hypothesis 13.3.1(1) asks only for a
member of `Lf(G,T)`. Lemma 13.3.2 subsequently supplies maximality.

This module currently establishes the selection step, not Theorem D.
The recognition inputs are Theorems 13.3.16, 13.6.1, 13.8.1, 14.4.14,
and 14.7.75, together with the list in Lemma 13.3.2.
-/

namespace CFSG.Quasithin.Chapter14.Section08

/-- The choice needed for Hypothesis 13.3.1(4). Applied to `Lf(G,T)`,
this avoids the maximal-member descent in the proof of Theorem 14.8.2.
No finiteness assumption is needed for this selection step. -/
public theorem exists_local_with_uniform_A5_quotient
    {G : Type*} [Group G] (localFamily : Set (Subgroup G))
    (hne : localFamily.Nonempty) :
    ∃ L ∈ localFamily,
      Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
        ∀ K ∈ localFamily,
          Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) := by
  classical
  by_cases h : ∃ L ∈ localFamily,
      ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  · obtain ⟨L, hL, hnot⟩ := h
    exact ⟨L, hL, fun hA5 => (hnot hA5).elim⟩
  · obtain ⟨L, hL⟩ := hne
    refine ⟨L, hL, fun _ K hK => ?_⟩
    by_contra hnot
    exact h ⟨K, hK, hnot⟩

end CFSG.Quasithin.Chapter14.Section08
