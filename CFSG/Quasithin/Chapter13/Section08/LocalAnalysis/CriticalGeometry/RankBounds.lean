module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.CommutatorComparison
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.RankOne
public import Theory.Representation.BinaryOffender.Basic

/-!
# Rank bounds from the actual star images

The line-containment branch of 13.8.11(1) forces Uγ*<Vγ*: otherwise
comparison of star images bounds [U_H,Vγ] by Uγ, contradicting normal
generation. A nontrivial subgroup properly contained in an elementary
abelian group forces the latter's binary rank above one.

For 13.8.11(2), rank at most one makes Uγ*=Vγ* of order two. Corrected
13.8.10 then gives either V₁≤Uγ (excluded by the preceding argument) or
the actual transvection action with common axis Dγ. The rank is the
BinaryOffender rank used by the downstream component sieve.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.10–11,
printed p.950. The no-transvection-on-V_H/U_H branch of 13.8.11(1) still
requires transport of the quotient action; it is not asserted here.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
variable {G : Type*} [Group G] [Finite G]

def HasTransvectionAxis (P U D : Subgroup G) [IsElementaryAbelian 2 U]
    (hn : P ≤ normalizer (U : Set G)) : Prop :=
  FixedPoints.subgroup (conjugationAction P U hn).range U = D.subgroupOf U ∧
  (D.subgroupOf U).index = 2 ∧
  ∀ p : P, binaryLinear (conjugationAction P U hn p) ∈
    LinearEquiv.transvections (ZMod 2) (Additive U)

theorem rank_gt_one_of_nontrivial_lt (A B : Subgroup G)
    (hA : A ≠ ⊥) (hB : IsElementaryAbelian 2 B) (hAB : A < B) : 1 < rank B := by
  have hB' : IsElementaryTwo B := ⟨ne_bot_of_le_ne_bot hA hAB.le, hB⟩
  by_contra hn
  have hr : rank B = 1 := by have := hB'.rank_pos; omega
  have hc : Nat.card B = 2 := by simpa only [hr, pow_one] using hB'.card_eq_two_pow_rank
  have hd := card_dvd_of_le hAB.le
  rw [hc] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
  · exact hA (card_eq_one.mp he)
  · exact hAB.ne (eq_of_le_of_card_ge hAB.le (by rw [he, hc]))

omit [Finite G] in
theorem starImage_isElementaryAbelian (H X : Subgroup G)
    [IsElementaryAbelian 2 X] (hXH : X ≤ H) :
    IsElementaryAbelian 2 (Source.starImage H X) := by
  let _ : IsElementaryAbelian 2 (X.subgroupOf H) := IsElementaryAbelian.subgroupOf hXH
  exact IsElementaryAbelian.map _

/-- Strictness of the actual denominator detects a nontrivial star image. -/
theorem starImage_ne_bot_of_Dgamma_lt
    (H UH Uγ V₁ : Subgroup G) (hUγH : Uγ ≤ H)
    (hD : Source.Dgamma Uγ UH V₁ = Uγ ⊓ Source.QH H)
    (hproper : Source.Dgamma Uγ UH V₁ < Uγ) : Source.starImage H Uγ ≠ ⊥ := by
  intro he
  have hc : (Source.QH H).relIndex Uγ = 1 := by
    rw [← starImage_card H Uγ hUγH, he]
    exact Nat.card_unique
  have hle := relIndex_eq_one.mp hc
  exact hproper.not_ge (hD ▸ le_inf le_rfl hle)

theorem starImage_lt_of_noncentral_and_line
    (H F U V Z : Subgroup G) [IsElementaryAbelian 2 V]
    (hFH : F ≤ H) (hVH : V ≤ H) (hZH : Z ≤ H)
    (hZN : H ≤ normalizer (Z : Set G))
    (hUV : U ≤ V) (hVF : V ≤ normalizer (F : Set G))
    (hFU : F ≤ normalizer (U : Set G))
    (hFQ : ⁅F, Source.QH H⁆ ≤ Z) (hnoncentral : ¬ ⁅F, V⁆ ≤ U)
    (hstar : Source.starImage H U ≠ ⊥) (hZU : Z ≤ U) :
    Source.starImage H U < Source.starImage H V ∧ 1 < rank (Source.starImage H V) := by
  have hle : Source.starImage H U ≤ Source.starImage H V :=
    map_mono (subgroupOf_mono H hUV)
  have hlt : Source.starImage H U < Source.starImage H V := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hc := commutator_bound_of_equal_starImage H F U V Z hFH hVH hZH hZN hUV hVF hFQ heq
    exact hnoncentral (hc.trans (sup_le (le_normalizer_iff_commutator_le_right.mp hFU) hZU))
  exact ⟨hlt, rank_gt_one_of_nontrivial_lt _ _ hstar
    (starImage_isElementaryAbelian H V hVH) hlt⟩

theorem rank_gt_one_of_no_axis
    (H UH Uγ Vγ A₁ V₁ : Subgroup G)
    [IsElementaryAbelian 2 UH] [IsElementaryAbelian 2 Uγ] [IsElementaryAbelian 2 Vγ]
    (hUHH : UH ≤ H) (hVγH : Vγ ≤ H) (hV₁H : V₁ ≤ H)
    (hHN : H ≤ normalizer (V₁ : Set G))
    (hUV : Uγ ≤ Vγ) (hVU : Vγ ≤ normalizer (UH : Set G))
    (hn : UH ≤ normalizer (Uγ : Set G))
    (hQ : ⁅UH, Source.QH H⁆ ≤ V₁) (hnoncentral : ¬ ⁅UH, Vγ⁆ ≤ Uγ)
    (hstar : Source.starImage H Uγ ≠ ⊥)
    (hDγ : Source.Dgamma Uγ UH V₁ = Uγ ⊓ Source.QH H)
    (hproper : Source.DH UH Uγ A₁ < UH)
    (hcomparison : (Source.DH UH Uγ A₁).relIndex UH ≤
      (Source.Dgamma Uγ UH V₁).relIndex Uγ)
    (hline : Nat.card V₁ = 2)
    (hno : ¬ HasTransvectionAxis UH Uγ (Source.Dgamma Uγ UH V₁) hn) :
    1 < rank (Source.starImage H Vγ) := by
  have hle : Source.starImage H Uγ ≤ Source.starImage H Vγ :=
    map_mono (subgroupOf_mono H hUV)
  have hV : IsElementaryTwo (Source.starImage H Vγ) :=
    ⟨ne_bot_of_le_ne_bot hstar hle, starImage_isElementaryAbelian H Vγ hVγH⟩
  by_contra hr
  have hrank : rank (Source.starImage H Vγ) = 1 := by have := hV.rank_pos; omega
  have hcV : Nat.card (Source.starImage H Vγ) = 2 := by
    simpa only [hrank, pow_one] using hV.card_eq_two_pow_rank
  have hcU : Nat.card (Source.starImage H Uγ) = 2 := by
    have hd := card_dvd_of_le hle
    rw [hcV] at hd
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (fun he => hstar (card_eq_one.mp he))
  have heq : Source.starImage H Uγ = Source.starImage H Vγ :=
    eq_of_le_of_card_ge hle (by rw [hcU, hcV])
  have hcases := (corrected_rank_one_of_starImage H UH Uγ A₁ V₁ (hUV.trans hVγH)
    hcU hDγ hproper hcomparison hline hn ((hUV.trans hVγH).trans hHN)).2.2
  rcases hcases with hlineU | haxis
  · have hlt := (starImage_lt_of_noncentral_and_line H UH Uγ Vγ V₁ hUHH hVγH hV₁H
      hHN hUV hVU hn hQ hnoncentral hstar hlineU).1
    exact hlt.ne heq
  · exact hno haxis

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
end
