/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/RepresentationTheory/PrimeOrderIrreducibility.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic

/-!
# Prime-order irreducibility over the ternary field

Prime-order orbit counting restricts invariant subspace dimensions; injectivity of the difference operator supplies action commutators.

Source: Gerald Höhn, ATLAS, `Atlas/RepresentationTheory/PrimeOrderIrreducibility.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

/-!
# A prime-order criterion for irreducibility

A fixed-point-free operator of order eleven on a five-dimensional ternary
space has no proper nonzero invariant subspaces. The proof uses prime-order
orbit counting on each subspace, rather than a character table.
-/

namespace Atlas.RepresentationTheory

open Module

/-- Orbit counting for a linear operator whose only fixed vector is zero. -/
theorem card_modEq_one_of_prime_power
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype V]
    (s : Module.End K V) {p n : ℕ} [Fact p.Prime]
    (hs : s ^ (p ^ n) = 1) (hfix : ∀ v, s v = v → v = 0) :
    Fintype.card V ≡ 1 [MOD p] := by
  classical
  let f : Function.End V := fun v => s v
  have hf : f ^ (p ^ n) = 1 := by
    funext v
    change (s : V → V)^[p ^ n] v = v
    rw [← Module.End.pow_apply, hs, Module.End.one_apply]
  have h := Equiv.Perm.card_fixedPoints_modEq hf
  have he : f.fixedPoints = ({0} : Set V) := by
    ext v
    change s v = v ↔ v ∈ ({0} : Set V)
    simp only [Set.mem_singleton_iff]
    exact ⟨hfix v, fun hv => hv ▸ s.map_zero⟩
  simpa only [he, Fintype.card_unique] using h

/-- Any invariant subspace of a dimension-five ternary space under a
fixed-point-free operator whose eleventh power is one is zero or the whole space. -/
theorem ternary_finrank_five_invariant_eq_bot_or_top
    {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V]
    (hdim : finrank (ZMod 3) V = 5)
    (s : Module.End (ZMod 3) V) (hs : s ^ 11 = 1)
    (hfix : ∀ v, s v = v → v = 0)
    (W : Submodule (ZMod 3) V) (hW : ∀ v ∈ W, s v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  let t : Module.End (ZMod 3) W := s.restrict hW
  have ht : t ^ 11 = 1 := by
    ext v
    have hcomm : Function.Semiconj (Subtype.val : W → V) t s := fun _ => rfl
    have hv := hcomm.iterate_right 11 v
    simpa only [← Module.End.pow_apply, hs, Module.End.one_apply] using hv
  have htfix : ∀ v, t v = v → v = 0 := by
    intro v hv
    apply Subtype.ext
    exact hfix v (congrArg Subtype.val hv)
  let : Fintype W := Fintype.ofEquiv (Fin (finrank (ZMod 3) W) → ZMod 3)
    (Module.finBasis (ZMod 3) W).equivFun.symm.toEquiv
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hc := card_modEq_one_of_prime_power t (p := 11) (n := 1) (by simpa using ht) htfix
  rw [Module.card_eq_pow_finrank (K := ZMod 3), ZMod.card] at hc
  have hle : finrank (ZMod 3) W ≤ 5 := W.finrank_le.trans_eq hdim
  have hd : finrank (ZMod 3) W = 0 ∨ finrank (ZMod 3) W = 5 := by
    have numerical : ∀ d : Fin 6, 3 ^ d.val % 11 = 1 → d.val = 0 ∨ d.val = 5 := by decide
    exact numerical ⟨finrank (ZMod 3) W, by omega⟩ hc
  rcases hd with hd | hd
  · exact Or.inl (Submodule.finrank_eq_zero.mp hd)
  · exact Or.inr (Submodule.eq_top_of_finrank_eq (hd.trans hdim.symm))

/-- A fixed-point-free endomorphism on a finite-dimensional space has
surjective difference from the identity. Thus every vector is an action
commutator difference for that one operator. -/
theorem difference_surjective_of_fixed_eq_zero
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (s : Module.End K V) (hfix : ∀ v, s v = v → v = 0) :
    Function.Surjective (fun v => s v - v) := by
  have hinj : Function.Injective (s - (1 : Module.End K V)) := by
    intro u v huv
    have hz : (s - 1) (u - v) = 0 := by
      rw [map_sub, huv, sub_self]
    have hzero : u - v = 0 := hfix _ (sub_eq_zero.mp hz)
    exact sub_eq_zero.mp hzero
  exact LinearMap.surjective_of_injective hinj

/-- The span of action differences is the whole module if it contains the
differences of a fixed-point-free operator. -/
theorem span_differences_eq_top_of_fixed_eq_zero
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (s : Module.End K V) (hfix : ∀ v, s v = v → v = 0) :
    Submodule.span K (Set.range (fun v => s v - v)) = ⊤ := by
  rw [(difference_surjective_of_fixed_eq_zero s hfix).range_eq]
  exact Submodule.span_univ

/-- A finite-order operator of order invertible in the field has no
nontrivial Jordan extension of its fixed subspace: a vector fixed modulo
a pointwise fixed submodule is already fixed. -/
theorem fixed_of_difference_mem_fixed_submodule
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (s : Module.End K V) (W : Submodule K V)
    (hW : ∀ w ∈ W, s w = w) {n : ℕ} (hn : (n : K) ≠ 0)
    (hs : s ^ n = 1) {v : V} (hv : s v - v ∈ W) : s v = v := by
  let w := s v - v
  have hw : s w = w := hW w hv
  have hit : ∀ m : ℕ, (s ^ m) v = v + (m : K) • w := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      simp only [map_add, map_smul, hw, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      dsimp [w]
      module
  have hz : (n : K) • w = 0 := by
    have h := hit n
    rw [hs, Module.End.one_apply] at h
    exact add_left_cancel (h.symm.trans (add_zero v).symm)
  have hwzero : w = 0 := (smul_eq_zero.mp hz).resolve_left hn
  exact sub_eq_zero.mp hwzero

end Atlas.RepresentationTheory
