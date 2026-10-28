module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FinCases

/-!
# Exterior-square fixed spaces of a binary `5 + 5 + 1` permutation basis

The permutation `(0 1 2 3 4)(5 6 7 8 9)` has eleven orbits on unordered
pairs. Averaging over its five powers maps the exterior basis into the span
of eleven orbit sums. Every fixed vector is its own average in characteristic
two, proving the fixed-dimension upper bound on the actual exterior power.
The finite certificate only enumerates pairs of eleven indices; all exterior
and averaging identities are proved structurally.

The remaining cyclic basis classification is published as an explicit
contract, separate from this proved calculation. The native application in
`FiveSpace.ExteriorBound` uses dimension eleven and fixed dimension three.

Source: the order-five step of Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, M₂₄ paragraph, manuscript p.17.
-/

@[expose] public section
open scoped BigOperators
open Module
namespace Representation.MathieuM24Degree44.FiveSpace.ExteriorBound

universe u

/-- Two five-cycles and one fixed basis vector. -/
def cycle : Fin 11 → Fin 11 := ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5, 10]
private def pairs : Fin 11 → Fin 11 × Fin 11 :=
  ![(0,1), (0,2), (5,6), (5,7), (0,5), (0,6), (0,7), (0,8), (0,9), (0,10), (5,10)]

set_option maxRecDepth 4096 in
private lemma pair_coverage (i j : Fin 11) (h : i ≠ j) :
    ∃ r : Fin 11, ∃ k : Fin 5,
      ((cycle^[k.val]) (pairs r).1 = i ∧ (cycle^[k.val]) (pairs r).2 = j) ∨
      ((cycle^[k.val]) (pairs r).1 = j ∧ (cycle^[k.val]) (pairs r).2 = i) := by
  revert i j
  decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private def normFive (f : Module.End (ZMod 2) V) : Module.End (ZMod 2) V :=
  ∑ k ∈ Finset.range 5, f ^ k

private lemma normFive_mul (f : Module.End (ZMod 2) V) (hf : f ^ 5 = 1) :
    normFive f * f = normFive f := by
  calc
    normFive f * f = ∑ k ∈ Finset.range 5, f ^ (k + 1) := by
      simp only [normFive, Finset.sum_mul, pow_succ]
    _ = normFive f := by
      have hh := Finset.sum_range_succ' (fun k : ℕ => f ^ k) 5
      rw [Finset.sum_range_succ, hf, pow_zero] at hh
      exact add_right_cancel hh.symm

private lemma normFive_pow (f : Module.End (ZMod 2) V) (hf : f ^ 5 = 1) (n : ℕ) :
    normFive f * f ^ n = normFive f := by
  induction n with
  | zero => simp
  | succ n hn => rw [pow_succ, ← mul_assoc, hn, normFive_mul f hf]

private lemma normFive_fixed (f : Module.End (ZMod 2) V) (v : V) (hv : f v = v) :
    normFive f v = v := by
  have hp (n : ℕ) : (f ^ n) v = v := by
    induction n with
    | zero => rfl
    | succ n hn => rw [pow_succ, Module.End.mul_apply, hv, hn]
  simp only [normFive, LinearMap.sum_apply, hp, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), show ((5 : ℕ) : ZMod 2) = 1 by decide, one_smul]


private def wedge (v w : V) : ⋀[ZMod 2]^2 V :=
  exteriorPower.ιMulti (ZMod 2) 2 ![v,w]

private lemma wedge_self (v : V) : wedge v v = 0 := by
  exact (exteriorPower.ιMulti (ZMod 2) 2).map_eq_zero_of_eq ![v,v]
    (i := 0) (j := 1) rfl (by decide)

private lemma wedge_swap (v w : V) : wedge w v = wedge v w := by
  have h := (exteriorPower.ιMulti (ZMod 2) 2).map_swap ![v,w]
    (i := 0) (j := 1) (by decide)
  have he : ![v,w] ∘ Equiv.swap (0 : Fin 2) 1 = ![w,v] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  change wedge w v = _ at h
  rw [← neg_one_smul (ZMod 2), show (-1 : ZMod 2) = 1 by decide, one_smul] at h
  exact h

private lemma map_wedge (f : Module.End (ZMod 2) V) (v w : V) :
    exteriorPower.map 2 f (wedge v w) = wedge (f v) (f w) := by
  rw [wedge, exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

private lemma map_pow (f : Module.End (ZMod 2) V) (n : ℕ) :
    exteriorPower.map 2 (f ^ n) = exteriorPower.map 2 f ^ n := by
  induction n with
  | zero => exact exteriorPower.map_id
  | succ n hn =>
    rw [pow_succ, pow_succ, ← hn]
    exact exteriorPower.map_comp f (f ^ n)
/-- The chosen permutation has period five. -/
theorem cycle_five (i : Fin 11) : (cycle^[5]) i = i := by
  revert i
  decide

private lemma pow_basis (f : Module.End (ZMod 2) V) (b : Basis (Fin 11) (ZMod 2) V)
    (hb : ∀ i, f (b i) = b (cycle i)) (n : ℕ) (i : Fin 11) :
    (f ^ n) (b i) = b ((cycle^[n]) i) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ', Module.End.mul_apply, hn, hb, Function.iterate_succ_apply']

private lemma pow_five (f : Module.End (ZMod 2) V) (b : Basis (Fin 11) (ZMod 2) V)
    (hb : ∀ i, f (b i) = b (cycle i)) : f ^ 5 = 1 := by
  apply b.ext
  intro i
  rw [pow_basis f b hb, cycle_five]
  rfl

/-- Eleven orbit averages span the fixed space of the literal exterior square. -/
theorem exterior_fixed_finrank_le (f : Module.End (ZMod 2) V)
    (b : Basis (Fin 11) (ZMod 2) V) (hb : ∀ i, f (b i) = b (cycle i)) :
    Module.finrank (ZMod 2) (LinearMap.ker (exteriorPower.map 2 f - 1)) ≤ 11 := by
  classical
  let E := exteriorPower.map 2 f
  let A := normFive E
  let u : Fin 11 → ⋀[ZMod 2]^2 V := fun r => A (wedge (b (pairs r).1) (b (pairs r).2))
  let S := Submodule.span (ZMod 2) (Set.range u)
  have he : E ^ 5 = 1 := by
    rw [← map_pow, pow_five f b hb]
    exact exteriorPower.map_id
  have hpow (n : ℕ) (i j : Fin 11) :
      (E ^ n) (wedge (b i) (b j)) =
        wedge (b ((cycle^[n]) i)) (b ((cycle^[n]) j)) := by
    change (exteriorPower.map 2 f ^ n) _ = _
    rw [← map_pow, map_wedge, pow_basis f b hb, pow_basis f b hb]
  have hmem (i j : Fin 11) : A (wedge (b i) (b j)) ∈ S := by
    by_cases hij : i = j
    · subst j
      rw [wedge_self, map_zero]
      exact S.zero_mem
    obtain ⟨r, k, hk | hk⟩ := pair_coverage i j hij
    · have h := hpow k.val (pairs r).1 (pairs r).2
      rw [hk.1, hk.2] at h
      rw [← h]
      change (normFive E * E ^ k.val) _ ∈ S
      rw [normFive_pow E he]
      exact Submodule.subset_span (Set.mem_range_self r)
    · rw [wedge_swap (b j) (b i)]
      have h := hpow k.val (pairs r).1 (pairs r).2
      rw [hk.1, hk.2] at h
      rw [← h]
      change (normFive E * E ^ k.val) _ ∈ S
      rw [normFive_pow E he]
      exact Submodule.subset_span (Set.mem_range_self r)
  have hrange : LinearMap.range A ≤ S := by
    rw [LinearMap.range_eq_map, Submodule.map_le_iff_le_comap]
    rw [← (b.exteriorPower 2).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    change A (b.exteriorPower 2 s) ∈ S
    let a := Set.powersetCard.ofFinEmbEquiv.symm s
    have hs : b.exteriorPower 2 s = wedge (b (a 0)) (b (a 1)) := by
      rw [exteriorPower.basis_apply]
      change exteriorPower.ιMulti (ZMod 2) 2 (b ∘ a) =
        exteriorPower.ιMulti (ZMod 2) 2 ![b (a 0), b (a 1)]
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [hs]
    exact hmem _ _
  have hker : LinearMap.ker (E - 1) ≤ S := by
    intro v hv
    have hv' : E v = v := sub_eq_zero.mp hv
    apply hrange
    exact ⟨v, normFive_fixed E v hv'⟩
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_basis b
  exact (Submodule.finrank_mono hker).trans (by
    simpa only [Set.finrank, S, Fintype.card_fin] using finrank_range_le_card u)

/-- A basis of the original vector space on which the given operator acts
as the two marked five-cycles and the fixed point. -/
def HasPermutationBasis (f : Module.End (ZMod 2) V) : Prop :=
  ∃ b : Basis (Fin 11) (ZMod 2) V, ∀ i, f (b i) = b (cycle i)

/-- The independent cyclic-module classification needed by the native
Golay application. This definition asserts no existence theorem. -/
def CyclicBasisClassification : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (f : Module.End (ZMod 2) V),
    f ^ 5 = 1 → Module.finrank (ZMod 2) V = 11 →
    Module.finrank (ZMod 2) (LinearMap.ker (f - 1)) = 3 →
      HasPermutationBasis f

end Representation.MathieuM24Degree44.FiveSpace.ExteriorBound
