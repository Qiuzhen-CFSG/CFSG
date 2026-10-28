module
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients
/-!
# Cubic movement bounds for small normal sections

Coprime additivity bounds cubic movement in a two-group of order at most 64
containing a normal subgroup of order eight. Injective homomorphisms preserve
the literal centralizer index. Above a two-core quotient of order three, this
index counts every complete noncentral two-chief series.

Source application: Aschbacher--Smith C.1.37 and 14.7.10, printed pp.141--143
and 1045. The natural-point consumer retains the actual kernel and subgroup maps.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement.CubicComparison
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem length_le_log_card (A R : Subgroup G) :
    conjugationCubicLength A R ≤ Nat.log 4 (Nat.card R) :=
  Nat.log_mono_right (Nat.le_of_dvd Nat.card_pos ((centralizer (A : Set G)).relIndex_dvd_card R))

theorem fixed_length_le_log_card {A W : Type*} [Group A] [Group W] [Finite W]
    [MulDistribMulAction A W] : FixedPoints.cubicLength A W ≤ Nat.log 4 (Nat.card W) :=
  Nat.log_mono_right (Nat.le_of_dvd Nat.card_pos (FixedPoints.subgroup A W).index_dvd_card)

omit [Finite G] [Finite H] in
theorem length_map_injective (f : G →* H) (hf : Function.Injective f)
    (A R : Subgroup G) :
    conjugationCubicLength (A.map f) (R.map f) = conjugationCubicLength A R := by
  have hc : (centralizer (A.map f : Set H)).comap f = centralizer (A : Set G) := by
    ext x
    constructor
    · intro hx a ha
      apply hf
      simpa only [map_mul] using hx (f a) (mem_map_of_mem f ha)
    · intro hx a ha
      obtain ⟨b,hb,rfl⟩ := ha
      simpa only [map_mul] using congrArg f (hx b hb)
  unfold conjugationCubicLength
  rw [← hc, relIndex_comap]

theorem section_length_le_log_card (A R N : Subgroup G)
    (hA : IsPGroup 3 A) (hR : IsPGroup 2 R) (hNR : N ≤ R)
    (hAR : A ≤ normalizer (R : Set G)) (hAN : A ≤ normalizer (N : Set G))
    [(N.subgroupOf R).Normal] :
    sectionCubicLength A N R ≤ Nat.log 4 (Nat.card (R ⧸ N.subgroupOf R)) := by
  let := quotientConjugationAction A R N hAR hAN
  rw [sectionCubicLength_eq_quotient_of_twoGroup A R N hA hR hNR hAR hAN]
  exact fixed_length_le_log_card

/-- A normal eight in a two-group of order at most 64 bounds its cubic length by two. -/
theorem length_le_two_of_normal_eight (A R N : Subgroup G)
    (hA : IsPGroup 3 A) (hR : IsPGroup 2 R) (hNR : N ≤ R)
    (hAR : A ≤ normalizer (R : Set G)) (hAN : A ≤ normalizer (N : Set G))
    [(N.subgroupOf R).Normal] (hN : Nat.card N = 8) (hcard : Nat.card R ≤ 64) :
    conjugationCubicLength A R ≤ 2 := by
  have hq : Nat.card (R ⧸ N.subgroupOf R) ≤ 8 := by
    have he := (N.subgroupOf R).index_mul_card
    rw [index_eq_card, Nat.card_congr (subgroupOfEquivOfLe hNR).toEquiv, hN] at he
    omega
  have hn := length_le_log_card A N
  rw [hN] at hn
  have hr := (section_length_le_log_card A R N hA hR hNR hAR hAN).trans
    (Nat.log_mono_right hq)
  norm_num at hn hr
  have hm := conjugationCubicLength_mono A hNR
  unfold sectionCubicLength at hr
  omega

/-- When the two-core quotient has order three, every complete chief count is
its actual cubic length, for any subgroup of order three. -/
theorem count_of_core_quotient_card_three (hq : Nat.card (G ⧸ pCore 2 G) = 3)
    (A : Subgroup G) (hA : Nat.card A = 3)
    (s : ChiefSeries G) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    s.noncentralTwoCount = conjugationCubicLength A (pCore 2 G) := by
  let f := QuotientGroup.mk' (pCore 2 G)
  have hp : IsPGroup 2 f.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have ht : Nat.card (⊤ : Subgroup (G ⧸ pCore 2 G)) = 3 := by rw [card_top,hq]
  have ha : A.map f = ⊤ := eq_of_le_of_card_ge le_top (by
    rw [GLS3.Chapter5.cubic_image_card_of_two_kernel f hp A hA, ht])
  exact complete_count_eq_length (f := f) (X := ⊤) (A := A)
    (pCore 2 G) pCore_isPGroup (QuotientGroup.mk'_surjective _) hp ht
    (IsPGroup.of_card (n := 0) (by simp))
    (IsPGroup.of_card (n := 1) (by simpa using hA)) ha
    (centralTwoChiefFactors_of_not_four_dvd (by rw [hq]; decide)) s h0 h1

end NoncentralChiefRefinement.CubicComparison
