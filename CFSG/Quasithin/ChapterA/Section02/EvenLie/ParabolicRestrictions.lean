module

public import Theory.SpecificGroups.BinaryLinear.EvenLieLevi
public import Theory.SpecificGroups.ProjectiveLinear.RootNormalizerTorus
public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer
public import Theory.SpecificGroups.SymplecticSix.BinaryThreeRank
public import Theory.SpecificGroups.SymplecticSix.FieldTransport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.Defs
import Mathlib.Tactic

/-!
# Linear parameters and rank-three symplectic restrictions in A.2.18

The existing root-normalizer tori force q = 2 for a quasithin linear group
of degree at least four or a symplectic group of rank at least three.
The binary two-block Levi obstruction then excludes every linear degree
at least six. All field witnesses and projective quotients are transported
by actual equivalences, giving the source parameter restrictions directly.

For Sp₆(2), the explicit three independent plane rotations give ordinary
3-rank at least three. This separates the weak and strong lists. Combining
it with the larger-field torus excludes every Sp₆(2ᵃ) from the strong list.
These are simple-model results. They do not assert the remaining parabolic
simple-section restrictions or the cover classification of A.2.18.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.2.18,
printed p.40 (refs/quasithin.pdf). Licensed ATLAS field transport is reused
through its attributed production module.
-/

public section

open Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The L₂(2) × Lₙ₋₂(2) parabolic excludes every binary linear degree at least six. -/
theorem binary_linear_degree_le_five (hG : IsQuasithin G) {d : ℕ}
    (hmodel : ClassicalGroup.IsPSL G d 2) : d ≤ 5 := by
  by_contra hd
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let eF := Theory.SpecificGroups.SymplecticSix.fieldEquivZModTwo F hcard
  exact BinaryLinear.EvenLieLevi.not_quasithin_projective (by omega : 6 ≤ d)
    (isQuasithin_of_equiv (e.trans (Atlas.fieldEquivPSL d eF)) hG)

private theorem charP_binary {F : Type*} [Field F] [Finite F] {a : ℕ}
    (ha : 0 < a) (hcard : Nat.card F = 2 ^ a) : CharP F 2 := by
  let : Fintype F := Fintype.ofFinite F
  apply ringChar.of_eq
  apply FiniteField.even_card_iff_char_two.mpr
  rw [← Nat.card_eq_fintype_card, hcard]
  exact Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp (even_two.pow_of_ne_zero (by omega)))

/-- The genuine rank-three split torus forces the binary prime field in linear degree ≥4. -/
theorem linear_exponent_eq_one (hG : IsQuasithin G) {d a : ℕ} (hd : 4 ≤ d)
    (ha : 0 < a) (hmodel : ClassicalGroup.IsPSL G d (2 ^ a)) : a = 1 := by
  by_contra hne
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let : CharP F 2 := charP_binary ha hcard
  have hq : 2 < Nat.card F := by
    rw [hcard]
    exact (by norm_num : (2 : ℕ) = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) (by omega : 1 < a)
  exact Theory.SpecificGroups.ProjectiveLinearRoot.not_quasithin k hq
    (isQuasithin_of_equiv e hG)

/-- All linear parameters needed by A.2.18, proved without smaller-section induction. -/
theorem linear_parameters (hG : IsQuasithin G) {d a : ℕ} (ha : 0 < a)
    (hmodel : ClassicalGroup.IsPSL G d (2 ^ a)) :
    d ≤ 3 ∨ (a = 1 ∧ d ≤ 5) := by
  by_cases hd : d ≤ 3
  · exact Or.inl hd
  · have ha1 := linear_exponent_eq_one hG (by omega : 4 ≤ d) ha hmodel
    refine Or.inr ⟨ha1, binary_linear_degree_le_five hG ?_⟩
    simpa only [ha1, pow_one] using hmodel

/-- The three inverse diagonal pairs force the binary prime field in symplectic rank ≥3. -/
theorem symplectic_exponent_eq_one (hG : IsQuasithin G) {r a : ℕ} (hr : 3 ≤ r)
    (ha : 0 < a) (hmodel : ClassicalGroup.IsPSp G r (2 ^ a)) : a = 1 := by
  by_contra hne
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let : CharP F 2 := charP_binary ha hcard
  have hq : 2 < Nat.card F := by
    rw [hcard]
    exact (by norm_num : (2 : ℕ) = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) (by omega : 1 < a)
  exact Theory.SpecificGroups.SymplecticRoot.not_quasithin k hq
    (isQuasithin_of_equiv e hG)

/-- The three independent plane rotations survive the literal projective quotient. -/
theorem symplectic_six_binary_three_rank (hmodel : ClassicalGroup.IsPSp G 3 2) :
    3 ≤ primeRank 3 G := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  rw [primeRank_equiv 3 (e.trans
    (Theory.SpecificGroups.SymplecticSix.pspFieldEquivZModTwo F hcard))]
  exact Theory.SpecificGroups.SymplecticSix.BinaryThreeRank.primeRank_three_ge

/-- Sp₆(2) belongs only to the weak list: its ordinary 3-rank is too large. -/
theorem not_stronglyQuasithin_symplectic_six_binary
    (hmodel : ClassicalGroup.IsPSp G 3 2) : ¬ IsStronglyQuasithin G := by
  intro h
  have := h 3 (by decide) (by decide)
  have := symplectic_six_binary_three_rank hmodel
  omega

/-- In every characteristic-two parameter the rank-three symplectic family
is excluded from the strong list, including the binary endpoint. -/
theorem not_stronglyQuasithin_symplectic_six {a : ℕ} (ha : 0 < a)
    (hmodel : ClassicalGroup.IsPSp G 3 (2 ^ a)) : ¬ IsStronglyQuasithin G := by
  intro h
  have ha1 := symplectic_exponent_eq_one h.quasithin (by decide) ha hmodel
  apply not_stronglyQuasithin_symplectic_six_binary (G := G) _ h
  simpa only [ha1, pow_one] using hmodel
end CFSG.Quasithin.ChapterA.Section02.EvenLie
