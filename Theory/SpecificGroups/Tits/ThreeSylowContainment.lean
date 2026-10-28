module

public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Soundness
public import Theory.SpecificGroups.Tits.RelativeSecondBlockLayers.SecondOrder

/-!
# The Tits Sylow-overgroup obstruction

A subgroup containing the marked Sylow two-subgroup and having no prime
order divisors except two and three lies in the second marked parabolic.
Consequently its order is not divisible by nine. This proves the requested
proper solvable overgroup restriction, with those two hypotheses unnecessary.

The genuine Parrott–Atlas isomorphism transfers the certified 1755-coset
cover. The five-coset normal form in the first parabolic then writes every
element as a Sylow factor times a tested representative. Removing the Sylow
factor keeps the representative in the overgroup. The point-orbit witnesses
exclude every representative outside the second parabolic, since they would
force a prime divisor five or thirteen in the overgroup's order.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`);
Parrott, *A Characterization of the Tits' Simple Group* (1972), §5, p.683.
This uses the certified concrete carriers and cover, without requiring the
disputed first-parabolic two-core data.
-/

open Theory.GroupTheory.CosetEnumeration
namespace Tits.ThreeSylowContainment
open Subgroup ExceptionalParabolics OuterOddSubgroups.OverlapCentralizers

private theorem mapped_eval (w : Word ParrottGenerator) :
    parrottFiniteImageEquiv (eval parrottGenerator w) =
      eval atlas1600ParrottAssignment w := by
  simp only [eval, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨a,b⟩ _
  cases b <;> simp [letterValue]

set_option maxRecDepth 30000 in
private theorem concrete_covers (x : ParrottGroup) :
    ∃ h : parrottR1Subgroup, ∃ i : Fin 1755,
      x = h.val * representative parrottGenerator R1Certificate.input (R1Certificate.index i) := by
  let C : ParrottR1CosetCover := {
    rep := fun i => representative parrottGenerator R1Certificate.input (R1Certificate.index i)
    initial := R1Certificate.initial
    initial_eq := by simp [representative, R1Certificate.initial_index, R1Certificate.model.zero]
    step := fun a => tablePermutation R1Certificate.table R1Certificate.inverse_table (a, true)
    transition := fun i a => by
      simpa only [Fact.Valid, Related, eval_singleton, letterValue, ↓reduceIte,
        tablePermutation, Equiv.coe_fn_mk] using R1Certificate.edges i a }
  exact C.covers x

/-- Every element is a Sylow normal form times a first-parabolic rotation
power times one of the certified ambient representative words. -/
private theorem sylow_coset_cover (x : Atlas1600Group) :
    ∃ (n : Fin 2048) (j : Fin 5) (i : ℕ),
      x = atlas1600SylowTwoNormalForm n * firstRotation ^ j.val *
        eval atlas1600ParrottAssignment (R1Certificate.input.reps.getD i []) := by
  obtain ⟨h, i, he⟩ := concrete_covers (parrottFiniteImageEquiv.symm x)
  have hxform : x = parrottFiniteImageEquiv h.val * parrottFiniteImageEquiv
      (representative parrottGenerator R1Certificate.input (R1Certificate.index i)) := by
    rw [← map_mul, ← he, MulEquiv.apply_symm_apply]
  have hh : parrottFiniteImageEquiv h.val ∈ first := by
    rw [← ReeLocalBlockOrders.first_map]
    exact mem_map_of_mem _ h.property
  obtain ⟨⟨n,j⟩, hnj⟩ := firstNormalForm_surjective ⟨parrottFiniteImageEquiv h.val, hh⟩
  have hnf := congrArg Subtype.val hnj
  change atlas1600SylowTwoNormalForm n * firstRotation ^ j.val =
    parrottFiniteImageEquiv h.val at hnf
  refine ⟨n, j, R1Certificate.index i, ?_⟩
  rw [hxform, ← hnf, representative, mapped_eval]

/-- Every overgroup of the marked Sylow subgroup whose order has only the
primes two and three lies in the second marked parabolic. -/
public theorem le_second_of_prime_divisors (H : Subgroup Atlas1600Group)
    (hS : atlas1600SylowTwoSubgroup ≤ H)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3) :
    H ≤ second := by
  intro x hx
  obtain ⟨n, j, i, he⟩ := sylow_coset_cover x
  have ht : firstRotation ^ j.val *
      eval atlas1600ParrottAssignment (R1Certificate.input.reps.getD i []) ∈ H := by
    apply (H.mul_mem_cancel_left (hS (atlas1600SylowTwoNormalForm_mem n))).mp
    simpa only [← mul_assoc, ← he] using hx
  have hs := Certificate.representative_mem_second H hS hprimes i j ht
  rw [he, mul_assoc]
  exact second.mul_mem (sylow_le_second (atlas1600SylowTwoNormalForm_mem n)) hs

/-- The genuine Sylow-overgroup containment required in the small-field
case of Aschbacher–Smith's Proposition 1.3.4. -/
public theorem containment (H : Subgroup Atlas1600Group)
    (_hproper : H ≠ ⊤) (_hsolvable : Group.IsSolvable H)
    (hS : atlas1600SylowTwoSubgroup ≤ H)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3) :
    H ≤ first ∨ H ≤ second :=
  Or.inr (le_second_of_prime_divisors H hS hprimes)

/-- In particular the order of such a Sylow overgroup is not divisible by nine. -/
public theorem nine_not_dvd (H : Subgroup Atlas1600Group)
    (hS : atlas1600SylowTwoSubgroup ≤ H)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3) :
    ¬ 9 ∣ Nat.card H := by
  intro hd
  have h := hd.trans (card_dvd_of_le (le_second_of_prime_divisors H hS hprimes))
  rw [RelativeSecondBlockLayers.second_card] at h
  norm_num at h

end Tits.ThreeSylowContainment
