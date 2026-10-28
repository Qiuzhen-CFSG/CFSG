module

public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Suborbits
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The two-space branch of the TI orbit geometry

Suppose that the actual orbit of the fixed space consists of the fixed space
and one further member `W`, and that `W` lies in the moved space.  The actor
then fixes `W` setwise.  Its transitivity on the nonzero moved vectors forces
`W` to be the whole moved space.  An element taking the fixed space to the
moved space therefore interchanges the two spaces.  Removing the odd part of
its order gives an actual two-element (of order a power of two) with the same
interchange action.

This is the two-space Step 2 branch of GLS, Number 2, Chapter C,
Proposition 14.2 (`refs/KGroup/GLS2/ChapterC.tex`).
-/

@[expose] public section
namespace Representation.GoldschmidtONan
open BinaryOffender RegularCyclicNormalClosure

variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

private theorem odd_power_map_of_swap
    (F D : Submodule (ZMod 2) V) (t : X)
    (hFD : F.map (ρ t) = D) (hDF : D.map (ρ t) = F) :
    ∀ k : ℕ, F.map (ρ (t ^ (2 * k + 1))) = D := by
  have hD2 : D.map (ρ (t ^ 2)) = D := by
    calc
      D.map (ρ (t ^ 2)) = (D.map (ρ t)).map (ρ t) := by
        rw [show t ^ 2 = t * t by simp [pow_two], orbit_map_mul]
      _ = F.map (ρ t) := by rw [hDF]
      _ = D := hFD
  intro k
  induction k with
  | zero => simpa using hFD
  | succ k ih =>
      rw [show 2 * (Nat.succ k) + 1 = 2 + (2 * k + 1) by omega]
      rw [pow_add, orbit_map_mul, ih, hD2]

private theorem odd_power_map_of_swap' 
    (F D : Submodule (ZMod 2) V) (t : X)
    (hFD : F.map (ρ t) = D) (hDF : D.map (ρ t) = F) :
    ∀ k : ℕ, D.map (ρ (t ^ (2 * k + 1))) = F := by
  have hF2 : F.map (ρ (t ^ 2)) = F := by
    calc
      F.map (ρ (t ^ 2)) = (F.map (ρ t)).map (ρ t) := by
        rw [show t ^ 2 = t * t by simp [pow_two], orbit_map_mul]
      _ = D.map (ρ t) := by rw [hFD]
      _ = F := hDF
  intro k
  induction k with
  | zero => simpa using hDF
  | succ k ih =>
      rw [show 2 * (Nat.succ k) + 1 = 2 + (2 * k + 1) by omega]
      rw [pow_add, orbit_map_mul, ih, hF2]

/--
The two-space Step 2 branch, before packaging it as `SwappedCase`.

The assumptions use the actual orbit and actual fixed/moved subspaces.  The
conclusion supplies both the identification `W = moved` and a concrete
power-of-two order element interchanging the two spaces.
-/
public theorem Input.two_space_swapped
    [Finite X] [Finite V] (h : Input ρ Y)
    {W : Submodule (ZMod 2) V}
    (horbit : fixedOrbit ρ Y = {fixedSpace ρ Y, W})
    (hWne : W ≠ fixedSpace ρ Y)
    (hW : W ≤ displacementSpan ρ Y ⊤) :
    W = displacementSpan ρ Y ⊤ ∧
      ∃ t : X, (∃ a : ℕ, orderOf t = 2 ^ a) ∧
        (fixedSpace ρ Y).map (ρ t) = displacementSpan ρ Y ⊤ ∧
        (displacementSpan ρ Y ⊤).map (ρ t) = fixedSpace ρ Y := by
  let F := fixedSpace ρ Y
  let D := displacementSpan ρ Y ⊤
  have hWmem : W ∈ fixedOrbit ρ Y := by
    rw [horbit]
    exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
  have hyW : ∀ y : Y, W.map (ρ (y : X)) = W := by
    intro y
    have hm := map_mem_fixedOrbit hWmem (y : X)
    rw [horbit] at hm
    rcases Set.mem_insert_iff.mp hm with hm | hm
    · exact False.elim ((map_actor_ne_fixed hWne y) hm)
    · exact Set.mem_singleton_iff.mp hm
  have hDW : D ≤ W := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (h.orbit_ne_bot hWmem)
    intro d hd
    by_cases hd0 : d = 0
    · simp [hd0]
    obtain ⟨y, hy⟩ := h.transitive w (hW hw) hw0 d hd hd0
    have hmem : d ∈ W.map (ρ (y : X)) := ⟨w, hw, hy⟩
    rw [hyW y] at hmem
    exact hmem
  have hWD : W = D := le_antisymm hW hDW
  have hDmem : D ∈ fixedOrbit ρ Y := by simpa [hWD] using hWmem
  have hDmem' := hDmem
  obtain ⟨t, ht⟩ := hDmem'
  have htFD : F.map (ρ t) = D := by simpa [F, D] using ht
  have htDmem : D.map (ρ t) ∈ fixedOrbit ρ Y := map_mem_fixedOrbit hDmem t
  have htDpair : D.map (ρ t) = F ∨ D.map (ρ t) = D := by
    have horbitD : fixedOrbit ρ Y = {F, D} := by simpa [F, D, hWD] using horbit
    rw [horbitD] at htDmem
    rcases Set.mem_insert_iff.mp htDmem with hm | hm
    · exact Or.inl hm
    · exact Or.inr (Set.mem_singleton_iff.mp hm)
  have htDF : D.map (ρ t) = F := by
    rcases htDpair with htDF | htDD
    · exact htDF
    · exfalso
      apply h.fixed_ne_moved
      apply orbit_map_injective t
      exact htFD.trans htDD.symm
  let n := orderOf t
  have hn : n ≠ 0 := (orderOf_pos t).ne'
  let m := n / 2 ^ n.factorization 2
  have hmdiv : m ∣ n := by
    exact Nat.ordCompl_dvd n 2
  have hm0 : m ≠ 0 := (Nat.ordCompl_pos 2 hn).ne'
  have hmOdd : Odd m := (Nat.coprime_ordCompl Nat.prime_two hn).odd_of_left
  obtain ⟨k, hk⟩ := hmOdd.exists_bit1
  let s := t ^ m
  have hsord : orderOf s = 2 ^ n.factorization 2 := by
    dsimp [s]
    rw [orderOf_pow_of_dvd hm0 hmdiv]
    exact (Nat.div_eq_iff_eq_mul_left (Nat.ordCompl_pos 2 hn) hmdiv).2
      (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
  have hsFD : F.map (ρ s) = D := by
    dsimp [s]
    rw [hk]
    exact odd_power_map_of_swap F D t htFD htDF k
  have hsDF : D.map (ρ s) = F := by
    dsimp [s]
    rw [hk]
    exact odd_power_map_of_swap' F D t htFD htDF k
  refine ⟨hWD, s, ?_, ?_, ?_⟩
  · exact ⟨n.factorization 2, hsord⟩
  · exact hsFD
  · exact hsDF

/-- Package `Input.two_space_swapped` as the source `SwappedCase`. -/
public theorem Input.swappedCase_of_two_space
    [Finite X] [Finite V] (h : Input ρ Y)
    {W : Submodule (ZMod 2) V}
    (horbit : fixedOrbit ρ Y = {fixedSpace ρ Y, W})
    (hWne : W ≠ fixedSpace ρ Y)
    (hW : W ≤ displacementSpan ρ Y ⊤) :
    SwappedCase ρ Y := by
  obtain ⟨hWD, t, htord, htF, htD⟩ := h.two_space_swapped horbit hWne hW
  refine ⟨?_, t, htord, ?_, ?_⟩
  · simpa [hWD] using horbit
  · simpa [hWD] using htF
  · simpa [hWD] using htD

end Representation.GoldschmidtONan
