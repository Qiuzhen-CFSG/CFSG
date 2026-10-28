module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Domain
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.ActorBounds
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.LargeDegree
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.PrimeThirteen

/-!
# The odd PSL₃ source exclusion at the FF threshold

Three conjugates of an involution generate over the actual quasisimple
component. At quadratic ratio at most one, the proved ambient two-rank
bound therefore gives binary degree at most nine. The actual PSL₃(3)
quotient forces degree at least twelve through its element of order
thirteen; the larger primes have degree greater than eighteen.

This proves the B.4.2 exclusion on its original source domain, retaining
central covers and graph outer actors. The stronger cubic-threshold-two
assertion in K.2 has independent remaining degree-twelve calculations.

Source: Aschbacher–Smith B.4.2 and K.2; Guralnick–Malle,
Classification of 2F-modules I, Proposition 4.2 and (2.6).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The original FF action has degree at most nine, including graph actors. -/
theorem source_ff_degree_le_nine (ρ : Representation (ZMod 2) G V)
    (h : SourceAction ρ) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 p)
    (hff : IsFFModule ρ) : Module.finrank (ZMod 2) V ≤ 9 := by
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) :=
    h.quasisimple.simple
  let : Nontrivial (generalizedFitting G) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting G))).nontrivial
  have hc : cubicRatio ρ ≤ (1 : ENNReal) := (cubicRatio_le_quadraticRatio ρ).trans
    ((isFFModule_iff_quadraticRatio_le_one ρ).mp hff)
  have hb := finrank_le_of_cubicRatio_le_of_conjugates (m := 1) ρ (generalizedFitting G)
    (fixedSpace_eq_bot_of_faithful_irreducible_on ρ _ h.faithful h.irreducible)
    (source_three_conjugates_pslThree ρ h hp ho hm)
    (source_two_rank_pslThree ρ h hp ho hm) (by simpa only [Nat.cast_one] using hc)
  norm_num at hb
  exact hb

/-- Every odd-prime PSL₃ central quotient is excluded at the FF threshold. -/
theorem source_not_ff (ρ : Representation (ZMod 2) G V)
    (h : SourceAction ρ) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 p) :
    ¬ IsFFModule ρ := by
  intro hff
  have hb := source_ff_degree_le_nine ρ h hp ho hm hff
  by_cases he : p = 3
  · subst p
    have hl := source_degree_at_least_twelve ρ h hm
    omega
  · have hp2 := hp.two_le
    have hpne : p ≠ 2 := by intro h; subst p; norm_num at ho
    have hp4 : p ≠ 4 := by intro h; subst p; norm_num at hp
    have hl := source_degree_gt_eighteen ρ h hp (by omega) hm
    omega

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree

namespace CFSG.Quasithin.ChapterB.SourceClassification
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Literal B.4.2 application with its specified quasisimple layer. -/
theorem not_ff_odd_psl3 (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 3 p) : ¬ IsFFModule ρ := by
  rcases h with ⟨hsq,hfit,hquasi,hfaith,hirr,_⟩
  subst L
  exact ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.source_not_ff
    ρ ⟨hsq,hquasi,hfaith,hirr⟩ hp ho hm

/-- Exclude the odd PSL₃ family directly from an original best offender. -/
theorem not_odd_psl3_of_bestOffender (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSL (L ⧸ center L) 3 p := by
  intro hm
  exact not_ff_odd_psl3 (source_hypotheses_of_bestOffender hsq hfit hL hf hi hA)
    hp ho hm ⟨A,hA.isOffender ρ⟩

end CFSG.Quasithin.ChapterB.SourceClassification
