module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Bounds
public import Theory.GroupTheory.Hall.OddSylowComplement


/-!
# A nontrivial odd complement in the actual centralizer

Solvability of J gives an odd complement to its supplied Sylow two-subgroup
U. The common prime dividing |J| and q-1 prevents this complement from
being trivial, since a two-group has no such prime divisor. The result is
a literal ambient product J = UY and applies without normality of U.

This constructs the odd complement used in GLS4, Chapter 2, Lemma 14.8.
The further Suzuki-model assertion that U is normal when |U| > 2 is
separate; it is not assumed to follow from solvability or this factorization.
Source: refs/KGroup/GLS4/Chapter2.tex, Lemmas 14.3(b), 14.4(b), and 14.8.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

public theorem SylowGeometry.exists_nontrivial_odd_complement
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) :
    ∃ Y : Subgroup G, Y ≤ centralizer (residualGenerated M z t : Set G) ∧
      Y ≠ ⊥ ∧ Odd (Nat.card Y) ∧
        (centralizer (residualGenerated M z t : Set G) : Set G) =
          (g.U : Set G) * (Y : Set G) := by
  let J := centralizer (residualGenerated M z t : Set G)
  obtain ⟨V, hV⟩ := g.U_sylow_centralizer
  obtain ⟨Y0, hodd, hcomp⟩ := exists_odd_complement_sylow_two g.centralizer_solvable V
  let Y := Y0.map J.subtype
  have hYcard : Nat.card Y = Nat.card Y0 := card_map_of_injective J.subtype_injective
  have hVcard : Nat.card V = Nat.card g.U := by
    rw [← hV, card_map_of_injective J.subtype_injective]
  have hcard : Nat.card g.U * Nat.card Y = Nat.card J := by
    rw [hYcard, ← hVcard]
    exact hcomp.card_mul_card
  have hYne : Y ≠ ⊥ := by
    intro hYbot
    have hcY : Nat.card Y = 1 := (Subgroup.card_eq_one).mpr hYbot
    rw [hcY, mul_one] at hcard
    obtain ⟨p, hp, hpJ, hpq⟩ := s.common_prime
    obtain ⟨k, hk⟩ := V.isPGroup'.exists_card_eq
    rw [← hcard, ← hVcard, hk] at hpJ
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow hpJ)
    have hqodd : Odd (2 ^ (2 * m + 1) - 1) := Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero even_two (by omega)) odd_one
    exact (Nat.not_even_iff_odd.mpr hqodd) (even_iff_two_dvd.mpr (hp2 ▸ hpq))
  refine ⟨Y, map_subtype_le _, hYne, hYcard ▸ hodd, ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨⟨u, y⟩, huy, _⟩ := hcomp.existsUnique (⟨x, hx⟩ : J)
    exact ⟨u, hV ▸ mem_map_of_mem J.subtype u.property,
      y, mem_map_of_mem J.subtype y.property, congrArg Subtype.val huy⟩
  · rintro _ ⟨u, hu, y, hy, rfl⟩
    exact J.mul_mem (g.U_le_centralizer hu) (map_subtype_le Y0 hy)

end BenderSuzuki.ZD.SuzukiExclusion
