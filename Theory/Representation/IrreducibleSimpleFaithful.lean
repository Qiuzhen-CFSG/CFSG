module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Faithfulness of irreducible representations of simple groups

Over any field, an irreducible representation of a simple group in dimension
greater than one is faithful. The kernel is either trivial or the whole group.
In the latter case every line is invariant, contradicting irreducibility.
No assumption on the characteristic or the order of the group is needed.

This supplies the elementary faithfulness step following the modular-character
construction in Janko's uniqueness argument; see Gorenstein, *Finite Groups*,
§16.6, pp.482–483.
-/

namespace Representation

/-- Irreducibility in dimension greater than one forces faithfulness for a
simple group, including in modular characteristic. -/
public theorem injective_of_simple_of_irreducible_of_one_lt_finrank
    {F G V : Type*} [Field F] [Group G] [IsSimpleGroup G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [IsIrreducible ρ]
    (hdim : 1 < Module.finrank F V) : Function.Injective ρ := by
  classical
  rcases (MonoidHom.normal_ker ρ).eq_bot_or_eq_top with hker | hker
  · exact ρ.ker_eq_bot_iff.mp hker
  have htriv (g : G) : ρ g = 1 :=
    show g ∈ ρ.ker from hker ▸ Subgroup.mem_top g
  let b := Module.finBasis F V
  let i : Fin (Module.finrank F V) := ⟨0, lt_trans Nat.zero_lt_one hdim⟩
  let W : Subrepresentation ρ :=
    { toSubmodule := Submodule.span F {b i}
      apply_mem_toSubmodule := by
        intro g v hv
        simpa only [htriv, Module.End.one_apply] using hv }
  have hWne : W ≠ ⊥ := by
    intro hW
    have hv : b i ∈ W := Submodule.subset_span (Set.mem_singleton (b i))
    rw [hW] at hv
    exact b.ne_zero i hv
  have hWtop : W = ⊤ := (eq_bot_or_eq_top W).resolve_left hWne
  have he : W.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule hWtop
  have hd : Module.finrank F W.toSubmodule = 1 := finrank_span_singleton (b.ne_zero i)
  rw [he, finrank_top] at hd
  exact (ne_of_gt hdim hd).elim

end Representation
