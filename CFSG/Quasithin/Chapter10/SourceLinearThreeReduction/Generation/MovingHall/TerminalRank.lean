module

public import Theory.GroupTheory.CentralizingTorusRank
public import Theory.SpecificGroups.Classical.PairedOddRank
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank.Divisibility
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models

/-!
# The terminal odd-rank contradiction at arbitrary even field order

For every prime dividing q-1, the actual SL₃(q) and PSL₃(q) models have
prime rank at least two. Away from three this follows from the split torus;
at three the diagonal and cycle witness survives the scalar quotient.
A torus of order q-1 acting faithfully on S supplies an independent direction
when the linear-three subgroup centralizes S and that torus. Their join
therefore contradicts the SQTK hypothesis on the literal Borel normalizer.

This is the last step of Aschbacher--Smith 10.2.3, printed p.747. The
geometric construction and recognition of the overcomponent remain separate
inputs. No assumption that three divides q-1, or that q=4, is made.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- Rank two for the precise prime supplied by the original split torus. -/
theorem linear_three_primeRank_ge_two (K : Subgroup G) {q p : ℕ}
    (hp : p.Prime) (hd : p ∣ q - 1)
    (hmodel : IsSL K 3 q ∨ ClassicalGroup.IsPSL K 3 q) :
    2 ≤ primeRank p K := by
  rcases hmodel with hSL | hPSL
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hSL
    rw [primeRank_equiv p e]
    exact Theory.SpecificGroups.Classical.PairedOddRank.linear_special_of_dvd hp
      (hF ▸ hd)
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hPSL
    rw [primeRank_equiv p e]
    by_cases h3 : p = 3
    · subst p
      exact Theory.SpecificGroups.SignedThreeCubicRank.linear_projective_of_three_dvd
        (hF ▸ hd)
    · exact Theory.SpecificGroups.Classical.PairedOddRank.linear_projective_of_dvd hp h3
        (hF ▸ hd)

/-- The same odd prime contributes one torus direction and two model directions. -/
theorem terminal_oddRank_contradiction
    (I A K : Subgroup G) (hI : IsStronglyQuasithin I)
    (hAI : A ≤ I) (hKI : K ≤ I)
    (hdisjoint : Disjoint A K) (hcommute : A ≤ centralizer (K : Set G))
    {n : ℕ} (hn : 1 < n) (hA : 2 ^ n - 1 ∣ Nat.card A)
    (hmodel : IsSL K 3 (2 ^ n) ∨ ClassicalGroup.IsPSL K 3 (2 ^ n)) : False := by
  have hgt : 1 < 2 ^ n - 1 := by
    have hh := Nat.pow_lt_pow_right (a := 2) (by decide) hn
    norm_num at hh
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : 2 ^ n - 1 ≠ 1)
  let : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (2 ^ n - 1) := Nat.odd_iff.mpr (by
    have he := Nat.even_iff.mp (even_two.pow_of_ne_zero (by omega : n ≠ 0))
    have hpos : 0 < 2 ^ n := pow_pos (by decide) _
    omega)
  have hpodd : Odd p := hodd.of_dvd_nat hpd
  have hlarge := three_le_primeRank_of_disjoint_commuting A K hdisjoint hcommute
    (hpd.trans hA) (linear_three_primeRank_ge_two K hp hpd hmodel)
  have hle := Theory.GroupTheory.primeRank_le_of_injective p (inclusion (sup_le hAI hKI))
    (inclusion_injective (sup_le hAI hKI))
  have hsmall := hI p hp hpodd
  omega

/-- Source p.747 on the actual normalizer of the original Borel `S ⊔ A`. -/
theorem borel_normalizer_contradiction
    {𝒦 : GroupClass} (A K S : Subgroup G)
    (hI : IsSQTK 𝒦 (normalizer ((S ⊔ A : Subgroup G) : Set G)))
    (hfaithful : A ⊓ centralizer (S : Set G) = ⊥)
    (hcentral : K ≤ centralizer ((S ⊔ A : Subgroup G) : Set G))
    {n : ℕ} (hn : 1 < n) (hA : Nat.card A = 2 ^ n - 1)
    (hmodel : IsSL K 3 (2 ^ n) ∨ ClassicalGroup.IsPSL K 3 (2 ^ n)) : False := by
  have hKS : K ≤ centralizer (S : Set G) :=
    hcentral.trans (centralizer_le (fun _ hx => mem_sup_left hx))
  have hKA : K ≤ centralizer (A : Set G) :=
    hcentral.trans (centralizer_le (fun _ hx => mem_sup_right hx))
  have hAK : A ≤ centralizer (K : Set G) := by
    intro a ha k hk
    exact (hKA hk a ha).symm
  exact terminal_oddRank_contradiction
    (normalizer ((S ⊔ A : Subgroup G) : Set G)) A K hI.stronglyQuasithin
    (le_sup_right.trans (S ⊔ A).le_normalizer)
    (hcentral.trans (Subgroup.centralizer_le_normalizer _))
    (disjoint_of_centralizes_faithful_subgroup A K S hfaithful hKS) hAK hn
    (by rw [hA]) hmodel

end CFSG.Quasithin.Chapter10.MovingHall
