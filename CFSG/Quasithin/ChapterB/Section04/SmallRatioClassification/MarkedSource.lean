module
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.MarkedOdd
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.MarkedExceptional
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Ratios
/-!
# The odd and exceptional B.4 branches for the original marked chief action

The literal B.4 input and quadratic bound supply Chapter K's source domain.
The retained chief-image involution has order two and displacement rank at
most two. Applying the source exclusions to this same action removes odd
PSL₃, triality and Ree, and leaves only the three small odd-PSL₂ coincidences.
This consumer preserves the existing universal B.4.5 interface; it is the
specialized branch used by the original chief-action catalogue assembly.

Source: Aschbacher–Smith B.4.5 and K.2–3, printed pp.87,453–457.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [Finite V]
  {ρ : Representation (ZMod 2) G V}

/-- The actual numerical B.4 input on the same faithful chief-image action. -/
theorem rankOne_source_of_b4_quadratic
    (h : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2) :
    ChapterK.RankOne.SourceHypotheses ρ (generalizedFitting G) :=
  ⟨h.sqtk,rfl,h.quasisimple,h.faithful,h.irreducible,(Representation.BinaryOffender.cubicRatio_le_quadraticRatio ρ).trans hq⟩

/-- The exact odd and exceptional branch restrictions for the literal chief action. -/
theorem marked_b4_odd_exceptional_source
    (h : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2)
    (t : G) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2) :
    (∀ (p e : ℕ), p.Prime → Odd p → e ≤ 2 →
      ClassicalGroup.IsPSL ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 (p^e) →
        (p=5 ∧ e=1) ∨ (p=7 ∧ e=1) ∨ (p=3 ∧ e=2)) ∧
    (∀ p : ℕ, p.Prime → Odd p →
      ¬ ClassicalGroup.IsPSL ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 p) ∧
    (∀ n : ℕ, 0<n →
      ¬ _root_.Triality.Standard.IsTrialityGroupAt (2^n)
        ((generalizedFitting G) ⧸ center (generalizedFitting G))) ∧
    (∀ m : ℕ, 1≤m →
      ¬ Nonempty (((generalizedFitting G) ⧸ center (generalizedFitting G)) ≃* _root_.ReeF4.Model m)) := by
  have hs := rankOne_source_of_b4_quadratic h hq
  refine ⟨?_,?_,?_,?_⟩
  · intro p e hp ho he hm
    exact odd_pslTwo_theoremC_parameters_of_small_involution hs t ht hr hp ho he hm
  · intro p hp ho hm
    exact odd_pslThree_excluded_of_small_involution hs hp ho hm t ht hr
  · intro n hn hm
    exact triality_excluded_of_small_involution hs n hn hm t ht hr
  · rintro m hm ⟨e⟩
    exact reeF4_excluded_of_small_involution hs hm e t ht hr
end CFSG.Quasithin.ChapterB.SmallRatioClassification
