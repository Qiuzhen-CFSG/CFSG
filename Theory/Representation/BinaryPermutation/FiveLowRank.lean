module

public import Theory.Representation.BinaryPermutation
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Rank-one actors on the five-point binary core

The displacements of the four vectors eᵢ + e₄ distinguish every permutation
except the identity and a single transposition from rank-one operators.
Only these four vectors and the 120 permutations enter the finite check.
Faithfulness on the same vectors gives positive moved rank for every
nonidentity actor.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, the A₅-module
inspection in 14.4.6(a), printed p.1008.
-/

public section
namespace BinaryPermutation.FiveLowRank
private def basisVector (i : Fin 4) : core (Fin 5) :=
  ⟨Pi.single i.castSucc 1 + Pi.single 4 1, by
    simp [mem_core, Finset.sum_add_distrib, show (1 : ZMod 2) + 1 = 0 from rfl]⟩
private def delta (g : Equiv.Perm (Fin 5)) (i : Fin 4) : Full (Fin 5) :=
  (coreRepresentation (Fin 5) g (basisVector i) - basisVector i).val
private theorem inspection : ∀ g : Equiv.Perm (Fin 5),
    (∀ i j, delta g i = 0 ∨ delta g j = 0 ∨ delta g i = delta g j) →
    g = 1 ∨ ∃ i j : Fin 5, i ≠ j ∧ g = Equiv.swap i j := by decide +kernel
private theorem identity_test : ∀ g : Equiv.Perm (Fin 5),
    (∀ i, delta g i = 0) → g = 1 := by decide +kernel

/-- Rank at most one forces identity or a single transposition. -/
theorem low_rank (g : Equiv.Perm (Fin 5))
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range (coreRepresentation (Fin 5) g - LinearMap.id)) ≤ 1) :
    g = 1 ∨ ∃ i j : Fin 5, i ≠ j ∧ g = Equiv.swap i j := by
  let ρ := coreRepresentation (Fin 5)
  let t : core (Fin 5) ≃ₗ[ZMod 2] core (Fin 5) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (core (Fin 5)) (ρ.asGroupHom g)
  obtain ⟨φ, v, ht⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr (show
    Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 1 from hr)
  have hd (x : core (Fin 5)) : ρ g x - x = φ x • v := by
    have hx := congrArg (fun l : core (Fin 5) →ₗ[ZMod 2] core (Fin 5) => l x) ht
    change ρ g x = _ at hx
    rw [hx, LinearMap.transvection.apply, add_sub_cancel_left]
  have small (i : Fin 4) : delta g i = 0 ∨ delta g i = v.val := by
    have h := congrArg Subtype.val (hd (basisVector i))
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (φ (basisVector i)) with hz | ho
    · left; simpa [hz, ρ, delta] using h
    · right; simpa [ho, ρ, delta] using h
  apply inspection g
  intro i j
  rcases small i with hi | hi
  · exact Or.inl hi
  rcases small j with hj | hj
  · exact Or.inr (Or.inl hj)
  · exact Or.inr (Or.inr (hi.trans hj.symm))

/-- Every nonidentity permutation moves a nonzero core vector. -/
theorem rank_pos (g : Equiv.Perm (Fin 5)) (hg : g ≠ 1) :
    0 < Module.finrank (ZMod 2)
      (LinearMap.range (coreRepresentation (Fin 5) g - LinearMap.id)) := by
  by_contra! h
  have hb : LinearMap.range (coreRepresentation (Fin 5) g - LinearMap.id) = ⊥ :=
    Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero h)
  apply hg
  apply identity_test g
  intro i
  have hi : coreRepresentation (Fin 5) g (basisVector i) - basisVector i ∈
      LinearMap.range (coreRepresentation (Fin 5) g - LinearMap.id) := ⟨basisVector i, rfl⟩
  rw [hb, Submodule.mem_bot] at hi
  exact congrArg Subtype.val hi
end BinaryPermutation.FiveLowRank
