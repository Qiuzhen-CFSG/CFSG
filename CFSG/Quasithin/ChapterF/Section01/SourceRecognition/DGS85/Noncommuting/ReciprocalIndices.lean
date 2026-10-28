module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.CoreIntersections
public import Theory.Representation.BinaryConjugationSection.FixedQuotientIndex
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator

/-!
# Reciprocal indices at noncommuting critical centers

Mutual placement in the two local actors makes the two abelian centers act
quadratically on one another's literal sections. The actor-image order is
its core index, while the fixed-space quotient order is at most the original
centralizer index. Two applications of the preceding quadratic-module lower
estimate force all these quantities to agree. Noncommutation makes their
common value exceed one, supplying the strict inequality for recognition.

Source: DGS, *Groups and Graphs* (1985),7.1, printed p.126. The corrected
5.12(a) estimates remain explicit earlier-source inputs here. Their general
producer is `qt-dgs85-quadratic-modules`; generation for the source sections
is independently discharged in `SourceSections`.
-/

public section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G D₀ D₁ W₀ W₁ : Type*} [Group G] [Group D₀] [Group D₁]
  [AddCommGroup W₀] [Module (ZMod 2) W₀]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]

private theorem relIndex_eq_of_inf_eq (A B C : Subgroup G)
    (he : C ⊓ A = C ⊓ B) : A.relIndex C = B.relIndex C := by
  rw [← inf_relIndex_left C A, he, inf_relIndex_left]

/-- The reciprocal part of DGS7.1. The two lower estimates are the respective
applications of corrected5.12(a); all counting and strictness are proved here
for the original section coordinates and actor maps. -/
theorem reciprocal_section_indices
    (L₀ L₁ Q₀ Q₁ Z₀ Z₁ C₀ C₁ : Subgroup G) [Finite Z₀] [Finite Z₁]
    (σ₀ : Representation (ZMod 2) D₀ W₀) (π₀ : L₀ →* D₀)
    (σ₁ : Representation (ZMod 2) D₁ W₁) (π₁ : L₁ →* D₁)
    (d₀ : BinaryConjugationSection L₀ Z₀ C₀ (σ₀.comp π₀))
    (d₁ : BinaryConjugationSection L₁ Z₁ C₁ (σ₁.comp π₁))
    (h₁₀ : Z₁ ≤ L₀) (h₀₁ : Z₀ ≤ L₁)
    (hk₀ : π₀.ker = Q₀.subgroupOf L₀) (hk₁ : π₁.ker = Q₁.subgroupOf L₁)
    (hc₀ : Z₁ ⊓ centralizer (Z₀ : Set G) = Z₁ ⊓ Q₀)
    (hc₁ : Z₀ ⊓ centralizer (Z₁ : Set G) = Z₀ ⊓ Q₁)
    (hne : ⁅Z₀,Z₁⁆ ≠ ⊥)
    (hb₀ : Nat.card ((Z₁.subgroupOf L₀).map π₀) ≤
      Nat.card (W₀ ⧸ fixedSpace σ₀ ((Z₁.subgroupOf L₀).map π₀)))
    (hb₁ : Nat.card ((Z₀.subgroupOf L₁).map π₁) ≤
      Nat.card (W₁ ⧸ fixedSpace σ₁ ((Z₀.subgroupOf L₁).map π₁))) :
    (centralizer (Z₀ : Set G)).relIndex Z₁ = (centralizer (Z₁ : Set G)).relIndex Z₀ ∧
      Nat.card ((Z₁.subgroupOf L₀).map π₀) = Nat.card ((Z₀.subgroupOf L₁).map π₁) ∧
      Nat.card (W₀ ⧸ fixedSpace σ₀ ((Z₁.subgroupOf L₀).map π₀)) =
        Nat.card ((Z₁.subgroupOf L₀).map π₀) ∧
      Nat.card (W₁ ⧸ fixedSpace σ₁ ((Z₀.subgroupOf L₁).map π₁)) =
        Nat.card ((Z₀.subgroupOf L₁).map π₁) ∧
      Nat.card (W₀ ⧸ fixedSpace σ₀ ((Z₁.subgroupOf L₀).map π₀)) <
        Nat.card ((Z₁.subgroupOf L₀).map π₀) ^ 2 ∧
      Nat.card (W₁ ⧸ fixedSpace σ₁ ((Z₀.subgroupOf L₁).map π₁)) <
        Nat.card ((Z₀.subgroupOf L₁).map π₁) ^ 2 := by
  have hi₀ : Nat.card ((Z₁.subgroupOf L₀).map π₀) =
      (centralizer (Z₀ : Set G)).relIndex Z₁ :=
    (actor_image_card_eq_relIndex L₀ Q₀ Z₁ π₀ hk₀ h₁₀).trans
      (relIndex_eq_of_inf_eq _ _ _ hc₀).symm
  have hi₁ : Nat.card ((Z₀.subgroupOf L₁).map π₁) =
      (centralizer (Z₁ : Set G)).relIndex Z₀ :=
    (actor_image_card_eq_relIndex L₁ Q₁ Z₀ π₁ hk₁ h₀₁).trans
      (relIndex_eq_of_inf_eq _ _ _ hc₁).symm
  have hu₀ := fixed_quotient_card_le_centralizer_index σ₀ π₀ d₀ Z₁
  have hu₁ := fixed_quotient_card_le_centralizer_index σ₁ π₁ d₁ Z₀
  have he : (centralizer (Z₀ : Set G)).relIndex Z₁ =
      (centralizer (Z₁ : Set G)).relIndex Z₀ := by
    apply Nat.le_antisymm
    · exact hi₀ ▸ hb₀.trans hu₀
    · exact hi₁ ▸ hb₁.trans hu₁
  have hcard : Nat.card ((Z₁.subgroupOf L₀).map π₀) =
      Nat.card ((Z₀.subgroupOf L₁).map π₁) := hi₀.trans (he.trans hi₁.symm)
  have he₀ : Nat.card (W₀ ⧸ fixedSpace σ₀ ((Z₁.subgroupOf L₀).map π₀)) =
      Nat.card ((Z₁.subgroupOf L₀).map π₀) := by
    apply Nat.le_antisymm _ hb₀
    rw [hi₀, he]
    exact hu₀
  have he₁ : Nat.card (W₁ ⧸ fixedSpace σ₁ ((Z₀.subgroupOf L₁).map π₁)) =
      Nat.card ((Z₀.subgroupOf L₁).map π₁) := by
    apply Nat.le_antisymm _ hb₁
    rw [hi₁, ← he]
    exact hu₁
  have hgt : 1 < Nat.card ((Z₁.subgroupOf L₀).map π₀) := by
    rw [hi₀]
    apply Nat.one_lt_iff_ne_zero_and_ne_one.mpr
    refine ⟨index_ne_zero_of_finite, ?_⟩
    intro hone
    apply hne
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
    exact relIndex_eq_one.mp hone
  refine ⟨he, hcard, he₀, he₁, ?_, ?_⟩
  · rw [he₀, pow_two]
    simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hgt (by omega :
      0 < Nat.card ((Z₁.subgroupOf L₀).map π₀))
  · rw [he₁, ← hcard, pow_two]
    simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hgt (by omega :
      0 < Nat.card ((Z₁.subgroupOf L₀).map π₀))

/-- Mutual normalization of the two elementary centers gives quadratic action
on both literal sections; no quotient denominator is discarded. -/
theorem critical_sections_quadratic
    (L₀ L₁ Z₀ Z₁ C₀ C₁ : Subgroup G)
    [IsMulCommutative Z₀] [IsMulCommutative Z₁]
    (σ₀ : Representation (ZMod 2) D₀ W₀) (π₀ : L₀ →* D₀)
    (σ₁ : Representation (ZMod 2) D₁ W₁) (π₁ : L₁ →* D₁)
    (d₀ : BinaryConjugationSection L₀ Z₀ C₀ (σ₀.comp π₀))
    (d₁ : BinaryConjugationSection L₁ Z₁ C₁ (σ₁.comp π₁))
    (h₁₀ : Z₁ ≤ L₀) (h₀₁ : Z₀ ≤ L₁) :
    IsQuadratic σ₀ ((Z₁.subgroupOf L₀).map π₀) ∧
      IsQuadratic σ₁ ((Z₀.subgroupOf L₁).map π₁) := by
  have hz₀ : ⁅Z₀,Z₁⁆ ≤ Z₀ :=
    le_normalizer_iff_commutator_le_left.mp (h₁₀.trans d₀.normalized)
  have hz₁ : ⁅Z₁,Z₀⁆ ≤ Z₁ :=
    le_normalizer_iff_commutator_le_left.mp (h₀₁.trans d₁.normalized)
  constructor
  · apply isQuadratic_of_triple_commutator_le L₀ Z₀ C₀ Z₁ σ₀ π₀ d₀
    exact (commutator_mono le_rfl hz₁).trans
      ((commutator_self_eq_bot_iff.mpr inferInstance).le.trans bot_le)
  · apply isQuadratic_of_triple_commutator_le L₁ Z₁ C₁ Z₀ σ₁ π₁ d₁
    exact (commutator_mono le_rfl hz₀).trans
      ((commutator_self_eq_bot_iff.mpr inferInstance).le.trans bot_le)

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
