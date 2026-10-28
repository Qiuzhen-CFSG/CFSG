module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.MarkedImage
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SmallAlternating
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.PrimePSL2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuadraticPSL2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankTwoPerfect
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.G2Perfect
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Containing-model exclusions for the marked radical

Apply the full-Sylow overgroup results to the literal images B and D in
N/O₂(N). The Bender, binary unitary-cover and small alternating rows force
B = D. The prime and quadratic PSL₂ rows make B/O₂(B) quasisimple. Both
conclusions contradict the pre-embedding source data. For binary PSL₃,
PSp₄ and G₂, the preserved odd rank of B rules out every proper parabolic
overgroup, without assuming B quasisimple.

These exclusions remove containing carriers from the genuine Theorem C
catalogue. They do not assert the remaining case-ten extension or replace
the complete catalogue by a smaller ambient family.
Source: Aschbacher–Smith A.3.12, pp.47–48, and 1.3.8, p.513.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
open Section02 Section02.LocalModels ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
universe u
variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {p r : ℕ} {L : Subgroup G} {T : Sylow 2 G}
variable {C : Subgroup (radicalCore p L T)} {K : Subgroup G}

private theorem local_perfect {A : Type*} [Group A] {B S : Subgroup A}
    (hB : B ∈ localCComponents S) : Group.IsPerfect B := by
  let := hB.perfect
  let e := subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

/-- The containing image inherits the marked odd rank. -/
theorem SourceData.containing_image_rank (h : SourceData 𝒦 p r L T C K) :
    let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
    2 ≤ primeRank p (quotientImage K N) :=
  h.residual_image_rank.trans (primeRank_mono p (map_mono (comap_mono h.contains_Y)))

/-- All three Bender containing families are impossible on the literal image. -/
theorem SourceData.containing_not_bender (h : SourceData 𝒦 p r L T C K) :
    ¬ ClassificationModels.IsBenderModel
      (quotientImage K (normalizer (C.map (radicalCore p L T).subtype : Set G))) := by
  intro hm
  obtain ⟨S, _, hB, _, hBD, _, _, hD⟩ := h.marked_image_setup
  exact hBD.ne (eq_of_bender_containing_component S hB hD hBD.le hm)

/-- Binary special-unitary covers are excluded as covers, without
identifying them with their projective quotients. -/
theorem SourceData.containing_not_binary_su3 (h : SourceData 𝒦 p r L T C K)
    {n : ℕ} (hn : 0 < n) :
    ¬ IsSU (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) 3 (2 ^ n) := by
  intro hm
  obtain ⟨S, _, hB, _, hBD, _, _, hD⟩ := h.marked_image_setup
  exact hBD.ne (eq_of_binary_su3_containing_component S hB hD hBD.le hn hm)

/-- The small alternating groups and the genuine central cover 3.A₆
cannot be the containing image. -/
theorem SourceData.containing_not_small_alternating (h : SourceData 𝒦 p r L T C K) :
    let D := quotientImage K (normalizer (C.map (radicalCore p L T).subtype : Set G))
    ¬ (IsAlternating D 5 ∨ IsAlternating D 6 ∨ IsAlternatingCover D 6) := by
  intro D hm
  obtain ⟨S, _, hB, _, hBD, _, _, hD⟩ := h.marked_image_setup
  exact hBD.ne (eq_of_small_alternating_containing_component S hB hD hBD.le hm)

/-- The prime-field PSL₂ inspection contradicts the actual nonquasisimple
two-core quotient of the smaller image. -/
theorem SourceData.containing_not_prime_psl2 (h : SourceData 𝒦 p r L T C K)
    {q : ℕ} (hq : q.Prime) (ho : Odd q) :
    ¬ ClassicalGroup.IsPSL (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) 2 q := by
  intro hm
  obtain ⟨S, _, hB, _, hBD, hnot, _, hD⟩ := h.marked_image_setup
  let := local_perfect hB
  obtain ⟨_, hb⟩ := proper_primePSL2_models S hB hD hBD.le hBD.ne hq ho hm
  exact hnot (core_quasisimple (alternating_quasisimple hb (by decide)))

/-- The quadratic-field PSL₂ inspection gives the same contradiction. -/
theorem SourceData.containing_not_quadratic_psl2 (h : SourceData 𝒦 p r L T C K)
    {q : ℕ} (hq : q.Prime) (ho : Odd q) :
    ¬ ClassicalGroup.IsPSL (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) 2 (q ^ 2) := by
  intro hm
  obtain ⟨S, _, hB, _, hBD, hnot, _, hD⟩ := h.marked_image_setup
  let := local_perfect hB
  obtain ⟨hlarge, hb⟩ := proper_quadraticPSL2_models S hB hD hBD.le hBD.ne hq ho hm
  exact hnot (core_quasisimple (psl_quasisimple hb (.inr ⟨rfl, hlarge⟩)))

/-- Binary PSL₃ over fields larger than two is excluded by the actual
odd-rank-two perfect subgroup, including nonquasisimple smaller images. -/
theorem SourceData.containing_not_binary_psl3 (h : SourceData 𝒦 p r L T C K)
    {n : ℕ} (hn : 1 < n) :
    ¬ ClassicalGroup.IsPSL (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) 3 (2 ^ n) := by
  intro hm
  let : Fact p.Prime := ⟨h.prime⟩
  have ho : Odd p := h.prime.odd_of_ne_two (by have := h.large; omega)
  obtain ⟨S, _, hB, _, hBD, _, hrank, hD⟩ := h.marked_image_setup
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact hBD.ne (eq_of_linear_three_containing_component
    S hB hD hBD.le ho hrank hn hF e)

/-- The literal projective symplectic carrier is transported through the
proved characteristic-two equivalence with Sp₄. -/
theorem SourceData.containing_not_binary_psp4 (h : SourceData 𝒦 p r L T C K)
    {n : ℕ} (hn : 2 ≤ n) :
    ¬ ClassicalGroup.IsPSp (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) 2 (2 ^ n) := by
  intro hm
  let : Fact p.Prime := ⟨h.prime⟩
  have ho : Odd p := h.prime.odd_of_ne_two (by have := h.large; omega)
  obtain ⟨S, _, hB, _, hBD, _, hrank, hD⟩ := h.marked_image_setup
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
    omega
  exact hBD.ne (eq_of_symplectic_four_containing_component S hB hD hBD.le ho hrank
    hlarge (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm))

/-- Binary G₂ is excluded using odd rank, with no quasisimplicity
assumption on B or its two-core quotient. -/
theorem SourceData.containing_not_binary_g2 (h : SourceData 𝒦 p r L T C K)
    {n : ℕ} (hn : 2 ≤ n) :
    ¬ ClassificationModels.IsG2At (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) (2 ^ n) := by
  intro hm
  let : Fact p.Prime := ⟨h.prime⟩
  have ho : Odd p := h.prime.odd_of_ne_two (by have := h.large; omega)
  obtain ⟨S, _, hB, _, hBD, _, hrank, hD⟩ := h.marked_image_setup
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
    omega
  exact hBD.ne (eq_of_g2_containing_component_of_odd_rank S hB hD hBD.le ho hrank hlarge e)

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
