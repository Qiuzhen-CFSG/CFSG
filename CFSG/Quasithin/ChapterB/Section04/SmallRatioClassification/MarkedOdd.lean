module
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.OddRankOne
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.OddLinearFF
/-!
# Odd linear source exclusions from the original small involution

The actual chief action retains a nonidentity involution moving at most two
binary dimensions. Four conjugates of an outer involution in the PSL₂(25)
case would bound the whole irreducible degree by eight, whereas an inner
involution already moves at least six dimensions. The degree lower bound is
twelve. For odd PSL₃, three conjugates give degree at most six, contrary to
the original central-cover degree bounds. The existing cubic-ratio parameter
sieve then leaves exactly PSL₂(5), PSL₂(7) and PSL₂(9).

These source-specific exclusions retain the original group, representation
and quasisimple layer. The small involution is an actual witness, supplied by
the chief-image construction; no FF premise or broader 2F classification is
asserted. Source: Aschbacher–Smith B.4.5 and K.2, printed pp.87,453.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification
open ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem pslTwo_twentyFive_excluded_of_small_involution
    (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 25)
    (t : G) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2) : False := by
  rcases h with ⟨hsq,hfit,hquasi,hfaith,hirr,_⟩
  subst L
  let h : SourceAction ρ := ⟨hsq,hquasi,hfaith,hirr⟩
  have hsmall : fixedCodim ρ (zpowers t) ≤ 2 := by
    rwa [fixedCodim_zpowers_eq_displacement_rank]
  by_cases htL : t ∈ generalizedFitting G
  · have hl := RankOneSmall.TwentyFive.source_inner_displacement_ge_six ρ h hm htL ht
    omega
  · obtain ⟨g,hg⟩ := RankOneSmall.TwentyFive.source_outer_four_conjugates ρ h hm t htL
      (by rw [←ht];exact pow_orderOf_eq_one t)
    have hd := finrank_le_mul_fixedCodim_of_conjugate_generation ρ _
      (RankOneSize.source_fixedSpace_eq_bot ρ h) t g hg
    have hl := RankOneSmall.twelve_le_degree_twentyFive ρ hfaith hm
    omega

theorem odd_pslThree_excluded_of_small_involution
    (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 3 p)
    (t : G) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2) : False := by
  rcases h with ⟨hsq,hfit,hquasi,hfaith,hirr,_⟩
  subst L
  let h : SourceAction ρ := ⟨hsq,hquasi,hfaith,hirr⟩
  have ht1 : t ≠ 1 := by intro he; simp [he] at ht
  obtain ⟨g,hg⟩ := RankThree.source_three_conjugates_pslThree ρ h hp ho hm t ht1
    (by rw [←ht];exact pow_orderOf_eq_one t)
  have hd := finrank_le_mul_fixedCodim_of_conjugate_generation ρ _
    (RankOneSize.source_fixedSpace_eq_bot ρ h) t g hg
  rw [fixedCodim_zpowers_eq_displacement_rank] at hd
  change Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 2 at hr
  by_cases he : p = 3
  · subst p
    have hl := RankThree.source_degree_at_least_twelve ρ h hm
    omega
  · have hp2 := hp.two_le
    have hpne : p ≠ 2 := by intro hh;subst p;norm_num at ho
    have hp4 : p ≠ 4 := by intro hh;subst p;norm_num at hp
    have hl := RankThree.source_degree_gt_eighteen ρ h hp (by omega) hm
    omega

theorem odd_pslTwo_parameters_of_small_involution
    (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (t : G) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2)
    {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : e = 1 ∨ e = 2) (hlo : 4 ≤ p ^ e)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 (p ^ e)) :
    (p = 5 ∧ e = 1) ∨ (p = 7 ∧ e = 1) ∨ (p = 3 ∧ e = 2) := by
  have h25 : ¬ ClassicalGroup.IsPSL (L ⧸ center L) 2 25 :=
    fun hm => pslTwo_twentyFive_excluded_of_small_involution h hm t ht hr
  rcases h with ⟨hsq,hfit,hquasi,hfaith,hirr,hratio⟩
  subst L
  let h : SourceAction ρ := ⟨hsq,hquasi,hfaith,hirr⟩
  have hhi := RankOneSize.source_field_order_le_twentyFive ρ h hp ho he hlo hm hratio
  rcases prime_power_candidates_le_twentyFive hp ho he hlo hhi with hgood | hbad
  · exact hgood
  · exfalso
    rcases hbad with hq | hq | hq | hq | hq | hq
    · rw [hq] at hm
      exact (not_lt_of_ge hratio) (RankOneSmall.Eleven.two_lt_cubicRatio ρ h hm)
    · rw [hq] at hm
      exact (not_lt_of_ge hratio) (RankOneSmall.source_prime_exclusion ρ h (Or.inl rfl) hm)
    · rw [hq] at hm
      have hd := RankOneSmall.source_seventeen_degree_eq_eight ρ h hm hratio
      exact (not_lt_of_ge hratio)
        (RankOneSmall.Seventeen.two_lt_cubicRatio_of_degree_le_eight ρ h hm hd.le)
    · rw [hq] at hm
      exact (not_lt_of_ge hratio) (RankOneSmall.source_prime_exclusion ρ h (Or.inr (Or.inl rfl)) hm)
    · rw [hq] at hm
      exact (not_lt_of_ge hratio) (RankOneSmall.source_prime_exclusion ρ h (Or.inr (Or.inr rfl)) hm)
    · exact h25 (hq ▸ hm)
/-- The literal Theorem C odd-PSL₂ row supplies its positive field bounds. -/
theorem odd_pslTwo_theoremC_parameters_of_small_involution
    (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (t : G) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2)
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e ≤ 2)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 (p ^ e)) :
    (p = 5 ∧ e = 1) ∨ (p = 7 ∧ e = 1) ∨ (p = 3 ∧ e = 2) := by
  obtain ⟨he',hlo⟩ := SourceClassification.odd_pslTwo_source_bounds h hp ho he hm
  exact odd_pslTwo_parameters_of_small_involution h t ht hr hp ho he' hlo hm
end CFSG.Quasithin.ChapterB.SmallRatioClassification
