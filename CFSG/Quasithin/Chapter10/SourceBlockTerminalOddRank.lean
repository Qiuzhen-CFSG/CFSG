module

public import Theory.GroupTheory.CentralizingTorusRank
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models

/-!
# Terminal cubic-rank contradiction for the four-field block branch

The actual normalizer of the Borel subgroup `S ⊔ D` cannot contain an
(S)L₃(4) subgroup centralizing that Borel when `D` has order three and acts
faithfully on `S`. The matrix models supply rank two, while the faithful
action supplies an independent cubic direction. The resulting rank three
contradicts the normalizer's SQTK hypothesis.

These theorems consume the genuine earlier recognition and centralization
conclusions; they do not assert either producer. In source notation the
subgroups are `S₁`, `D₁`, and `L⁺`, and the normalizer is `M₁`.

Source: Aschbacher–Smith, proof of 10.2.3, printed pp.746–747, specialized
to `n = 2` for the natural A₅ branch of 10.2.12.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

theorem source_linear_three_four_primeRank_ge_two (K : Subgroup G)
    (hmodel : IsSL K 3 4 ∨ ClassicalGroup.IsPSL K 3 4) :
    2 ≤ primeRank 3 K := by
  rcases hmodel with hSL | hPSL
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hSL
    rw [primeRank_equiv 3 e]
    exact Theory.SpecificGroups.SignedThreeCubicRank.linear_special
      (n := 2) (by simpa using hF) (by decide)
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hPSL
    rw [primeRank_equiv 3 e]
    exact Theory.SpecificGroups.SignedThreeCubicRank.linear_projective
      (n := 2) (by simpa using hF) (by decide)

theorem source_block_terminal_cubic_contradiction
    (I D K : Subgroup G) (hI : IsStronglyQuasithin I)
    (hDI : D ≤ I) (hKI : K ≤ I)
    (hd : Disjoint D K) (hc : D ≤ centralizer (K : Set G))
    (hD : 3 ∣ Nat.card D)
    (hmodel : IsSL K 3 4 ∨ ClassicalGroup.IsPSL K 3 4) : False := by
  have hlarge := three_le_primeRank_of_disjoint_commuting D K hd hc hD
    (source_linear_three_four_primeRank_ge_two K hmodel)
  have hle := primeRank_le_of_injective 3 (inclusion (sup_le hDI hKI))
    (inclusion_injective (sup_le hDI hKI))
  have hsmall := hI 3 (by decide) (by decide)
  omega

theorem source_block_terminal_contradiction_of_faithful_borel
    (I D K S : Subgroup G) (hI : IsStronglyQuasithin I)
    (hDI : D ≤ I) (hKI : K ≤ I)
    (hfaithful : D ⊓ centralizer (S : Set G) = ⊥)
    (hcentral : K ≤ centralizer ((S ⊔ D : Subgroup G) : Set G))
    (hD : Nat.card D = 3)
    (hmodel : IsSL K 3 4 ∨ ClassicalGroup.IsPSL K 3 4) : False := by
  have hKS : K ≤ centralizer (S : Set G) :=
    hcentral.trans (centralizer_le (fun _ hx => mem_sup_left hx))
  have hKD : K ≤ centralizer (D : Set G) :=
    hcentral.trans (centralizer_le (fun _ hx => mem_sup_right hx))
  have hDK : D ≤ centralizer (K : Set G) := by
    intro d hd k hk
    exact (hKD hk d hd).symm
  exact source_block_terminal_cubic_contradiction I D K hI hDI hKI
    (disjoint_of_centralizes_faithful_subgroup D K S hfaithful hKS) hDK
    (by rw [hD]) hmodel

theorem source_block_borel_normalizer_contradiction
    {𝒦 : GroupClass} (D K S : Subgroup G)
    (hI : IsSQTK 𝒦 (normalizer ((S ⊔ D : Subgroup G) : Set G)))
    (hfaithful : D ⊓ centralizer (S : Set G) = ⊥)
    (hcentral : K ≤ centralizer ((S ⊔ D : Subgroup G) : Set G))
    (hD : Nat.card D = 3)
    (hmodel : IsSL K 3 4 ∨ ClassicalGroup.IsPSL K 3 4) : False := by
  exact source_block_terminal_contradiction_of_faithful_borel
    (normalizer ((S ⊔ D : Subgroup G) : Set G)) D K S hI.stronglyQuasithin
    (le_sup_right.trans (S ⊔ D).le_normalizer)
    (hcentral.trans (Subgroup.centralizer_le_normalizer _))
    hfaithful hcentral hD hmodel

end CFSG.Quasithin.Chapter10
