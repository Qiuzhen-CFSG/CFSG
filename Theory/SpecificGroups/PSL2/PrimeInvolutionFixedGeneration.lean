module
public import Theory.SpecificGroups.PSL2.PrimeInnerFixedGeneration
public import Theory.SpecificGroups.PSL2.SevenInvolutionGeneration
public import Theory.GroupAction.DihedralInnerInvolutions
public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex

/-!
# Dihedral involution fixed generation in prime PSL₂

For an adjacent-power prime, a faithful nonabelian dihedral two-group of
automorphisms generates PSL₂ through the fixed groups of its involutions.
The central half-turn is inner because it is a square and the outer quotient
has order two. For primes greater than nine, the centralizer of its inner
involution is maximal; a distinct acting involution cannot have its whole
fixed subgroup inside that centralizer.
The remaining prime seven is handled by the actual point and line parabolics
of PSL₂(7) ≃ SL₃(2).

This is the fixed-generation step in Aschbacher–Smith, Lemma 2.5.21,
printed p.566, for the faithful crossed dihedral action. It also supplies
the intrinsic Sylow-centralizer generation used in 2.5.19, printed p.564.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

/-- A faithful dihedral two-group of order at least eight generates an
adjacent-power prime PSL₂ through its involution fixed subgroups. -/
theorem prime_dihedral_involution_fixed_generation
    {p k : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (hpower : ∃ m : ℕ, p - 1 = 2 ^ m ∨ p + 1 = 2 ^ m)
    {P : Type*} [Group P] [Finite P] (hk : 2 ≤ k)
    (e : P ≃* DihedralGroup (2 ^ k))
    (f : P →* MulAut PSL(2, ZMod p)) (hf : Function.Injective f)
    (N : Subgroup PSL(2, ZMod p))
    (hfixed : ∀ i : P, orderOf i = 2 → (f i).fixedSubgroup ≤ N) : N = ⊤ := by
  by_cases hlarge : 9 < p
  · have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    obtain ⟨z, j, t, _, hz, hj, hjz, ht, hzt, _⟩ :=
      MulAut.dihedral_inner_involutions f hf hk e (psl2_center_eq_bot (ZMod p))
        (prime_card_inner_index (ZMod p) ho (by omega) (by simp))
    obtain ⟨m, hm⟩ := hpower
    apply prime_fixed_generation_of_inner_involution hlarge hm (f z) (f j)
      (by rw [← map_pow, (orderOf_eq_prime_iff.mp hj).1, map_one])
      (fun h => hjz (hf h)) t ht hzt N (hfixed z hz) (hfixed j hj)
  · have hprime : p.Prime := Fact.out
    have hp7 : p = 7 := by interval_cases p <;> norm_num at *
    subst p
    exact SevenInvolutionGeneration.fixed_generation_of_dihedral hk e f hf N hfixed

end Theory.PSL2
