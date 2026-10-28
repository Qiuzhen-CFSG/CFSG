module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FixedGeometry
public import CFSG.Quasithin.ChapterA.Section05To06.Ordering
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The order and rank of the central omega subgroup

The small-center alternative of 15.4.7 is incompatible with 15.4.11(2) and
the exclusion of the actual groups `L₃(2)` and `A₆`. Two different maximal
two-local overgroups of `C_G(Z)` also exclude `Z = 1`; together these give
`|Z| > 2`. Once the factor actions supply the one-coordinate index or the
two-coordinate swap witness, the fixed-index calculation and the distinct
overgroup argument give `|Z| = 4`, rank two, and fixed subgroups of order two.

The family argument takes raw preceding-theorem witnesses and does not define
a replacement for the source family `𝒴`. Its coordinate alternative must still
be constructed from 15.4.12(6); this module alone is not the source assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 15.4.14, printed p.1161.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors
open Subgroup
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The full exceptional alternatives of 15.4.7, together with the ordering
maximality in 15.4.11(2), give the lower bound needed in 15.4.14. All normalizers
of characteristic subgroups use their actual images in the ambient group. -/
theorem center_card_gt_two_from_small_center (T : Sylow 2 G)
    {M₁ M₂ : Subgroup G}
    (hM₁ : IsMaximalTwoLocal M₁) (hM₂ : IsMaximalTwoLocal M₂)
    (hC₁ : centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M₁)
    (hC₂ : centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M₂)
    (hne : M₁ ≠ M₂)
    (h11 : ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      IsOrderingMaximal T M)
    (h7 : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2 →
      (∃ C : Subgroup (ChapterB.baumann (T : Subgroup G)),
        C.Characteristic ∧ C ≠ ⊥ ∧ ∃ M : Subgroup G,
          (IsMaximalTwoLocal M ∧
            normalizer (C.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ≤ M) ∧
          (∀ N : Subgroup G, IsMaximalTwoLocal N →
            normalizer (C.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ≤ N → N = M) ∧
          IsOrderingMaximal T M ∧
          (∀ N : Subgroup G, IsOrderingMaximal T N → N = M)) ∨
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 6)))
    (hL : ¬ Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))
    (hA : ¬ Nonempty (G ≃* alternatingGroup (Fin 6))) :
    2 < Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) := by
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  have hTZ : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    intro t ht
    exact mem_centralizer_iff.mpr fun z hz =>
      (((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm
  have hnotbot : Z ≠ ⊥ := by
    intro hb
    have hCZ : centralizer (Z : Set G) = ⊤ := by
      apply top_unique
      intro x _
      apply mem_centralizer_iff.mpr
      intro z hz
      have hz1 : z = 1 := mem_bot.mp (hb ▸ hz)
      simp only [hz1, one_mul, mul_one]
    have h₁ : M₁ = ⊤ := top_unique (hCZ ▸ hC₁)
    have h₂ : M₂ = ⊤ := top_unique (hCZ ▸ hC₂)
    exact hne (h₁.trans h₂.symm)
  have hnotone : Nat.card Z ≠ 1 := fun h => hnotbot (card_eq_one.mp h)
  have hnottwo : Nat.card Z ≠ 2 := by
    intro htwo
    rcases h7 htwo with ⟨C, _, _, M, _, _, _, hu⟩ | h | h
    · exact hne ((hu M₁ (h11 M₁ hM₁ (hTZ.trans hC₁))).trans
        (hu M₂ (h11 M₂ hM₂ (hTZ.trans hC₂))).symm)
    · exact hL h
    · exact hA h
  have hpos : 0 < Nat.card Z := Nat.card_pos
  change 2 < Nat.card Z
  omega

/-- The family form of the 15.4.14 calculation, from raw local and coordinate
witnesses. In a source application `𝒴` must be the genuine family and the
coordinate alternative must be derived from 15.4.12, not assumed as a source
conclusion. The preceding theorem discharges `hlarge` using 15.4.7 and 15.4.11. -/
theorem center_geometry_of_factor_coordinates (T : Sylow 2 G)
    (𝒴 : Set (Subgroup G)) (overgroup : Subgroup G → Subgroup G)
    {M₁ M₂ : Subgroup G}
    (hM₁ : IsMaximalTwoLocal M₁) (hM₂ : IsMaximalTwoLocal M₂)
    (hC₁ : centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M₁)
    (hC₂ : centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M₂)
    (hne : M₁ ≠ M₂)
    (hunique : ∀ Y ∈ 𝒴, ∀ M : Subgroup G, IsMaximalTwoLocal M →
      Y ⊔ (T : Subgroup G) ≤ M → M = overgroup Y)
    (hexists : ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      ∃ Y ∈ 𝒴, Y ≤ M)
    (hcoords : ∀ Y ∈ 𝒴,
      ((ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (Y : Set G)).relIndex
        (ChapterB.thompsonAlpha (T : Subgroup G)) = 2) ∨
      Nonempty (SwappedBinaryQuotient (ChapterB.thompsonAlpha (T : Subgroup G))
        (T : Subgroup G) Y))
    (hlarge : 2 < Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G))) :
    let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
    Nat.card Z = 4 ∧ Group.rank Z = 2 ∧ primeRank 2 Z = 2 ∧
      ∀ Y ∈ 𝒴, (Z ⊓ centralizer (Y : Set G)).relIndex Z = 2 ∧
        Nat.card (Z ⊓ centralizer (Y : Set G) : Subgroup G) = 2 ∧
        Z ⊓ centralizer (Y : Set G) ≠ ⊥ := by
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let : IsElementaryAbelian 2 Z := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  have hZE : Z ≤ ChapterB.thompsonAlpha (T : Subgroup G) :=
    centralOmega_le_thompsonAlpha _
  have hTZ : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    intro t ht
    exact mem_centralizer_iff.mpr fun z hz =>
      (((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm
  have hindex (Y : Subgroup G) (hY : Y ∈ 𝒴) :
      (Z ⊓ centralizer (Y : Set G)).relIndex Z = 2 := by
    have hn := not_centralizes_of_distinct_overgroups hTZ (hunique Y hY)
      hM₁ hM₂ hC₁ hC₂ hne
    rcases hcoords Y hY with h | h
    · exact centralizer_index_two_of_single_factor hZE h hn
    · exact h.elim fun d => centralizer_index_two_of_swapped_quotient d hZE hTZ hn
  obtain ⟨X, hX, hXM⟩ := hexists M₁ hM₁ (hTZ.trans hC₁)
  obtain ⟨Y, hY, hYM⟩ := hexists M₂ hM₂ (hTZ.trans hC₂)
  have hMX := hunique X hX M₁ hM₁ (sup_le hXM (hTZ.trans hC₁))
  have hMY := hunique Y hY M₂ hM₂ (sup_le hYM (hTZ.trans hC₂))
  have hc : Nat.card Z = 4 := card_eq_four_of_unique_hyperplanes hTZ
    (hunique X hX) (hunique Y hY) (by rwa [← hMX, ← hMY])
    (hindex X hX) (hindex Y hY) hlarge
  obtain ⟨hr, hp⟩ := rank_eq_two_of_card_four Z hc
  exact ⟨hc, hr, hp, fun Y hY =>
    ⟨hindex Y hY, centralizer_card_two_of_hyperplane hc (hindex Y hY)⟩⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors
