module
public import Theory.Representation.BinaryPermutation.FiveAction
/-!
# Odd involutions and singular displacements in the five-point core

An odd involution on five letters is a transposition; its nonzero
displacements have weight two and are nonsingular. Thus an involution
whose displacements on a subspace lie in a singular line must be even
whenever that subspace has trivial pointwise fixer.

The checks use 120 permutations and 32 binary words, not subgroup lattices.
Source application: Aschbacher–Smith 13.5.7, printed pp.917–918.
-/
@[expose] public section
namespace BinaryPermutation.FiveOddInvolution
open Equiv
/-- Every odd involution on five letters is one transposition. -/
theorem even_or_swap (g : Perm (Fin 5)) (hg : g ^ 2 = 1) :
    g ∈ alternatingGroup (Fin 5) ∨ ∃ i j : Fin 5, i ≠ j ∧ g = swap i j := by
  have h : ∀ g : Perm (Fin 5), g ^ 2 = 1 →
      Perm.sign g = 1 ∨ ∃ i j : Fin 5, i ≠ j ∧ g = swap i j := by decide +kernel
  exact (h g hg).imp Perm.mem_alternatingGroup.mpr id
/-- A transposition's nonzero displacement is nonsingular. -/
theorem swap_fixed_of_singular_displacement (i j : Fin 5) (x : core (Fin 5))
    (hx : FiveGeometry.form (coreRepresentation (Fin 5) (swap i j) x - x) = 0) :
    coreRepresentation (Fin 5) (swap i j) x = x := by
  have h : ∀ (i j : Fin 5) (x : Full (Fin 5)),
      (∑ a : Fin 5, ∑ b : Fin 5 with a < b,
        (representation (Fin 5) (swap i j) x - x) a *
          (representation (Fin 5) (swap i j) x - x) b) = 0 →
        representation (Fin 5) (swap i j) x = x := by decide +kernel
  exact Subtype.ext (h i j x.val hx)
/-- Singular displacements on a subspace with trivial pointwise fixer force
an involution to be even. -/
theorem even_of_singular_displacements (W : Subgroup (Multiplicative (core (Fin 5))))
    (hW : ∀ p : Perm (Fin 5),
      (∀ x ∈ W, coreRepresentation (Fin 5) p x.toAdd = x.toAdd) → p = 1)
    (g : Perm (Fin 5)) (hg : g ^ 2 = 1)
    (hs : ∀ x ∈ W, FiveGeometry.form
      (coreRepresentation (Fin 5) g x.toAdd - x.toAdd) = 0) :
    g ∈ alternatingGroup (Fin 5) := by
  rcases even_or_swap g hg with he | ⟨i,j,_,rfl⟩
  · exact he
  · have he := hW (swap i j) (fun x hx => swap_fixed_of_singular_displacement i j x.toAdd (hs x hx))
    exact he ▸ (alternatingGroup (Fin 5)).one_mem
end BinaryPermutation.FiveOddInvolution
