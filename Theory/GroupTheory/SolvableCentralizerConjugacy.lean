module

public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Mathlib.GroupTheory.Solvable

/-!
# Solvable centralizers and conjugacy

Conjugation identifies the centralizers of conjugate elements. Consequently,
an element centralizing a nonsolvable subgroup cannot be conjugate to an
element with solvable centralizer. The proof uses the actual restricted
conjugation equivalence and the inclusion of that subgroup.

This is the terminal obstruction in Aschbacher–Smith, combined manuscript
of 1 March 2004, proof of Theorem 13.9.1, printed p.974 (PDF p.991).
-/

public section

namespace Theory.GroupTheory

open Subgroup CentralizerSmallKernelTransport

variable {G : Type*} [Group G]

/-- Solvability of an element centralizer is invariant under actual conjugacy. -/
theorem isSolvable_centralizer_of_isConj {z x : G}
    (hz : Group.IsSolvable (centralizer ({z} : Set G))) (h : IsConj z x) :
    Group.IsSolvable (centralizer ({x} : Set G)) := by
  let := hz
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact Group.isSolvable_of_surjective
    (f := (centralizerEquiv (MulAut.conj g) z).toMonoidHom)
    (centralizerEquiv (MulAut.conj g) z).surjective

/-- A centralizer containing a nonsolvable subgroup cannot belong to a
conjugacy class whose element centralizers are solvable. -/
theorem not_isConj_of_nonsolvable_subgroup_centralized
    {z x : G} (H : Subgroup G)
    (hz : Group.IsSolvable (centralizer ({z} : Set G)))
    (hH : ¬ Group.IsSolvable H) (hx : x ∈ centralizer (H : Set G)) :
    ¬ IsConj z x := by
  intro h
  let := isSolvable_centralizer_of_isConj hz h
  have hHC : H ≤ centralizer ({x} : Set G) := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hx y hy)
  exact hH (Group.isSolvable_of_isSolvable_injective (inclusion_injective hHC))

end Theory.GroupTheory
