module

public import Glauberman.SuzukiCharacterization.CommutatorSupport
public import Glauberman.SuzukiCharacterization.CharacterSelectionArithmetic
public import Theory.Character.ModularBlock.Congruence
public import Theory.Character.Multiplicity

/-!
# Conditional selection of a character with zero Sylow fixed space

The character restriction coefficients are natural numbers. Removing the
principal row from the weighted column identity gives total weighted mass
one and norm mass at most |P| - 1. The numerical selection lemma gives a row
of small degree; the restriction degree lower bound then forces its principal
multiplicity to vanish. The character average converts this to the required
zero sum over P.

The weighted column identity (Lemma 4.1 with (4.1)) and the restriction degree
bound (4.6) remain explicit hypotheses below. `ColumnIdentities` proves the weighted
identity and norm bound from `Hypotheses`, using the constructed
`CommutatorSupportData`; `RestrictionDegreeLowerBound` proves the degree bound.
`ZeroFixedCharacter` assembles these results without additional hypotheses.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
equations (4.1)–(4.7), pp. 89–90, saved at
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

open scoped BigOperators
open ModularBlock.PrincipalBlockConstruction
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace Glauberman.SuzukiCharacterization.CharacterSelection

/-- The actual restriction coefficients for the principal and chosen linear character. -/
public theorem exists_restriction_multiplicities
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (d : PrincipalCongruenceBlockData G) (s : CommutatorSupportData P) :
    ∃ c₀ c₁ : d.I → ℕ,
      (∀ i, scalarProduct P (fun x : P => d.chi i (ConjClasses.mk (x : G))) 1 = c₀ i) ∧
      (∀ i, scalarProduct P (fun x : P => d.chi i (ConjClasses.mk (x : G))) s.theta = c₁ i) := by
  have hr (i : d.I) : IsCharacter (fun x : P => d.chi i (ConjClasses.mk (x : G))) := by
    obtain ⟨n, ρ, hρ⟩ := (d.complete.1 i).1
    exact ⟨n, ρ.comp (P : Subgroup G).subtype, by rw [hρ]; rfl⟩
  have ht : IsCharacter s.theta := by
    obtain ⟨n, ρ, _, hρ⟩ := s.linear.1
    exact ⟨n, ρ, hρ⟩
  choose c₀ hc₀ using fun i => (hr i).scalarProduct_eq_nat principal_isCharacter
  choose c₁ hc₁ using fun i => (hr i).scalarProduct_eq_nat ht
  exact ⟨c₀, c₁, hc₀, hc₁⟩

/-- Equations (4.1)–(4.7), with the two substantive column inputs explicit. -/
public theorem exists_zero_sum_of_column_identities
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (d : PrincipalCongruenceBlockData G) (s : CommutatorSupportData P)
    (c₀ c₁ : d.I → ℕ)
    (hc₀ : ∀ i, scalarProduct P (fun x : P => d.chi i (ConjClasses.mk (x : G))) 1 = c₀ i)
    (hc₁ : ∀ i, scalarProduct P (fun x : P => d.chi i (ConjClasses.mk (x : G))) s.theta = c₁ i)
    (q : ℝ) (hq : 0 < q)
    (hweighted : ∑ i ∈ d.block,
      ((c₁ i : ℝ) - c₀ i) * Complex.normSq (d.chi i (ConjClasses.mk (s.v : G))) /
        (d.chi i (ConjClasses.mk 1)).re = 0)
    (hnorm : ∑ i ∈ d.block, Complex.normSq (d.chi i (ConjClasses.mk (s.v : G))) ≤ Nat.card P)
    (hlower : ∀ i ∈ d.block, 1 ≤ (c₁ i : ℤ) - c₀ i →
      (c₀ i : ℝ) + q + ((c₁ i : ℝ) - 1) * ((Nat.card P : ℝ) - 1) ≤
        (d.chi i (ConjClasses.mk 1)).re) :
    ∃ i ∈ d.block, ∑ x : P, d.chi i (ConjClasses.mk (x : G)) = 0 := by
  classical
  let : Fintype P := Fintype.ofFinite P
  have hpval (g : G) : d.chi d.principal (ConjClasses.mk g) = 1 := by
    rw [d.principal_eq]
    rfl
  have hc₀p : c₀ d.principal = 1 := by
    have hp := hc₀ d.principal
    simp only [hpval] at hp
    have he : scalarProduct P (fun _ => (1 : ℂ)) 1 = 1 := by simp [scalarProduct]
    have hp' : scalarProduct P (fun _ => (1 : ℂ)) 1 = (c₀ d.principal : ℂ) := by
      exact hp
    rw [he] at hp'
    exact_mod_cast hp'.symm
  have hc₁p : c₁ d.principal = 0 := by
    have hz := s.linear.1.scalarProduct_principal_eq_zero s.theta_ne_one
    have hz' : scalarProduct P 1 s.theta = 0 := by
      rw [← scalarProduct_conj, hz, star_zero]
    have hp := hc₁ d.principal
    simp only [hpval] at hp
    change scalarProduct P 1 s.theta = _ at hp
    rw [hz'] at hp
    exact_mod_cast hp.symm
  let M : ℝ := (Nat.card P : ℝ) - 1
  have hM : 0 < M := by
    have hdiv : 2 ∣ Nat.card P := by
      have hd := orderOf_dvd_natCard s.v
      rw [s.involution] at hd
      exact hd
    have hcard : 2 ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos hdiv
    dsimp [M]
    have hcard' : (2 : ℝ) ≤ Nat.card P := by exact_mod_cast hcard
    linarith
  have hweight : ∑ i ∈ d.block.erase d.principal,
      (((c₁ i : ℤ) - c₀ i : ℤ) : ℝ) *
        Complex.normSq (d.chi i (ConjClasses.mk (s.v : G))) /
        (d.chi i (ConjClasses.mk 1)).re = 1 := by
    rw [← Finset.sum_erase_add _ _ d.principal_mem] at hweighted
    simp only [hc₀p, hc₁p, Nat.cast_zero, Nat.cast_one, zero_sub, hpval,
      Complex.normSq_one, Complex.one_re, mul_one, div_one] at hweighted
    simp only [Int.cast_sub, Int.cast_natCast]
    linarith
  have hmass : ∑ i ∈ d.block.erase d.principal,
      Complex.normSq (d.chi i (ConjClasses.mk (s.v : G))) ≤ M := by
    rw [← Finset.sum_erase_add _ _ d.principal_mem] at hnorm
    simp only [hpval, Complex.normSq_one] at hnorm
    dsimp [M]
    linarith
  obtain ⟨i, hi, hci, hupper⟩ := exists_degree_le_coefficient_mul
    (d.block.erase d.principal) (fun i => (c₁ i : ℤ) - c₀ i)
    (fun i => Complex.normSq (d.chi i (ConjClasses.mk (s.v : G))))
    (fun i => (d.chi i (ConjClasses.mk 1)).re) M hM
    (fun i _ => Complex.normSq_nonneg _) (fun i _ => (d.complete.1 i).degree_re_pos)
    hweight hmass
  have hi' := (Finset.mem_erase.mp hi).2
  simp only [Int.cast_sub, Int.cast_natCast] at hupper
  have hz := principal_multiplicity_eq_zero (c₀ i) (c₁ i) q M
    (d.chi i (ConjClasses.mk 1)).re hq hM.le (hlower i hi' hci) hupper
  refine ⟨i, hi', (scalarProduct_principal_eq_zero_iff _).mp ?_⟩
  have ht := hc₀ i
  rw [hz, Nat.cast_zero] at ht
  exact ht

end Glauberman.SuzukiCharacterization.CharacterSelection
