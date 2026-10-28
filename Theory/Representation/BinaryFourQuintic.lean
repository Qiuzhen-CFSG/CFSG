module
public import Theory.Representation.NonsplitFour
public import Mathlib.Algebra.Field.ZMod
public import Theory.Representation.SubrepresentationLattice

/-!
# Quintic actors on binary four-spaces

A faithful binary representation of dimension four is irreducible whenever
five divides the acting group's order. Restrict to a subgroup of order five
and apply the nonsplit prime-order theorem: no proper invariant summand has
a faithful action in dimensions one, two or three.

The HS seed-row application uses this on the literal A5 and A6 residuals.
Source: Aschbacher--Smith 14.3.23--25, printed pp.1000--1001; the general
prime-order argument and its attribution are in NonsplitFour.
-/

public noncomputable section
open Subgroup Module
namespace Representation
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem binary_four_irreducible_of_five_dvd
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hd : finrank (ZMod 2) W = 4) (h5 : 5 ∣ Nat.card D) : IsIrreducible ρ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 5 h5
  let A := zpowers a
  let : Fintype A := Fintype.ofFinite A
  let : Nontrivial W := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank (ZMod 2) W)
  refine ⟨fun U => ?_⟩
  have h := invariant_eq_bot_or_top_of_prime_card_dvd_sq_add_one
    5 (by decide) (by decide) (show Nat.card A = 5 by rw [Nat.card_zpowers,ha])
    (ρ.comp A.subtype) (hf.comp A.subtype_injective) hd
    (by decide) (by decide) (by decide) U.toSubmodule
    (fun b w hw => U.apply_mem_toSubmodule b.val hw)
  rcases h with h | h
  · exact .inl (Subrepresentation.toSubmodule_injective h)
  · exact .inr (Subrepresentation.toSubmodule_injective h)
end Representation
