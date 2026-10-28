module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.Forward.Exclusion
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.Surviving

/-!
# The surviving refinement and radical of the original flag

Triangle exclusion removes the exceptional branch from the complete earlier
11.1.2 alternatives. The prime-model signalizer proof then puts the original
R₁ inside O∞(KT) in every surviving case. The containing component retains
normality relative to the point normalizer and centralizer; its normalization
by T follows from the original flag.

The registered earlier source implications remain with
qt-d-1222-shadow-components and qt-d-1222-natural-shadow-reduction.
OddIndex/CanonicalSource combines this refinement with both radical bounds
using the canonical A.3.6 action proof, without a Fitting-index premise.
Source: Aschbacher–Smith, 11.4.1(2–3), printed pp.775–776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
open LocalGeometry Triangle.Reselection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- On the unchanged chosen geometry, the proved triangle exclusion gives
the exact surviving list and the literal R₁ radical containment. -/
theorem ofFlag_refinement_and_radical_of_preceding_sources
    {L V : Subgroup G} (D : Chapter12.Section02.ChosenModule T L V)
    (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (K X : Subgroup G) (z : G) (H : Subgroup G)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hKC : K ≤ centralizer (f.Vi 0 : Set G)) (hAK : f.Li 0 ≤ K)
    (hKZ : K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G))
    (h701 : ∀ (J W : Subgroup G) (D_J : Chapter12.Section02.ChosenModule T J W),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent)
    (h325 : ∀ (J W : Subgroup G) (D_J : Chapter12.Section02.ChosenModule T J W),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      D_J.Source325Alternatives)
    (h1132 : ∀ (J W : Subgroup G) (D_J : Chapter12.Section02.ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput) (c_J : Coordinates D_J S_J.field)
      (f_J : InvariantFlag c_J) H,
      Hypothesis1131At D_J S_J (c_J.binarySubspace (f_J.space 0)) H →
      Proposition1132At D_J S_J (c_J.binarySubspace (f_J.space 0)) H)
    (h1122 : ∀ (J W : Subgroup G) (D_J : Chapter12.Section02.ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput),
      Nonempty (ChapterB.QuasisimpleSource.ActionEquiv D_J.centralQuotientAction
        (ChapterB.QuasisimpleSource.binaryG2 S_J.field)) →
      ChapterE.indexedWeakClosure W (T : Subgroup G) 0 ≤
          (T : Subgroup G) ⊓ centralizer (W : Set G) ∧
        @ChapterE.globalS G _ W D_J.elementary = (2 * S_J.field.degree : ℕ) ∧
        (2 * S_J.field.degree : ℕ∞) < ChapterE.globalR W)
    (href : Components.RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree) :
    Source.ClassicalRefinementCase L (f.Li 0) K 1 S.field.degree ∧
      (ofFlag S f X z H).R₁ ≤
        (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
          (K ⊔ (T : Subgroup G)).subtype := by
  have hc := classical_refinement_of_preceding_sources D S f K X hK hKZ
    h701 h325 h1132 h1122 href
  have hn : normalizer (f.Vi 0 : Set G) ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2
  have hKC' : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) K :=
    ⟨⟨hKC, hK.1.2.subgroupOf_of_le hKC (Subgroup.centralizer_le_normalizer _)⟩,
      (normal_subgroupOf_iff_le_normalizer hKC).mpr
        ((Subgroup.centralizer_le_normalizer _).trans hn)⟩
  have hA : f.Li 0 ≠ ⊥ := by
    intro he
    apply (flag_residual_mem_local D S f 0).1.ne_bot
    rw [he]
    exact bot_subgroupOf _
  exact ⟨hc, ofFlag_surviving_radical_containment S f X z H K hKC' hA hAK
    ((f.invariant 0).trans hn) hc⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
