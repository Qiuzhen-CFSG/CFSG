module
public import Theory.GroupAction.SymplecticSmallTwoSection

/-!
# The smallest two-section admitting a symplectic component action

A prime of binary multiplicative order 4n divides the order of Sp₄(2ⁿ).
It cannot divide the automorphism group of a two-group of order below q⁴.
Consequently a two-perfect cover of the simple symplectic group centralizes
any normalized section below that bound, including nonabelian sections and
sections with a central attachment.

The actual radius application is NonbinarySymplectic.CriticalReduction.RadiusGrowth.
Source: MS93 (5.7)--(5.8), printed pp.919--920; the binary primitive-prime
input is GLS2, Chapter A, Theorem 1.1.
-/

public section
open Subgroup
namespace Subgroup
variable {G S : Type*} [Group G] [Group S] [Finite S] [IsSimpleGroup S]

/-- A two-perfect cover of a simple symplectic group fixes every normalized
two-section of order strictly less than q⁴. -/
theorem commutator_component_le_of_symplectic_section_lt_fourth_power
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (hS : Nat.card S = Nat.card (Theory.SpecificGroups.SymplecticFour.Sp F))
    (L D Z : Subgroup G) [Finite L] [Finite D] [(Z.subgroupOf D).Normal]
    (hL : IsPPerfect 2 L) (q : L →* S) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker) (hD : IsPGroup 2 D)
    (hcard : Z.relIndex D < Nat.card F ^ 4)
    (hLD : L ≤ normalizer (D : Set G)) (hLZ : L ≤ normalizer (Z : Set G)) :
    ⁅D,L⁆ ≤ Z := by
  obtain ⟨p,hp,ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two_four_mul hn
  have hdiv : p ∣ Nat.card S := by
    rw [hS]
    exact Representation.SymplecticFour.prime_dvd_card_of_orderOf_two hn hF hp ho
  obtain ⟨m,hm⟩ := hD.index (Z.subgroupOf D)
  change Z.relIndex D = 2 ^ m at hm
  have hbound : m < 4 * n := by
    rw [hm,hF,←pow_mul] at hcard
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hcard
    omega
  exact commutator_component_le_of_primitive_small_section L D Z hL q hq hker
    hp hdiv hD hm.le (by rwa [ho]) hLD hLZ

end Subgroup
