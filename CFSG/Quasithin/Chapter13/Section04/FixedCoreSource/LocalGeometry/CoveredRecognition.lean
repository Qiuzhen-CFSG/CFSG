module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CoveredPointResidual
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CoveredSolvableReduction

/-!
# Fixed-module recognition after covered residual selection

Covered 13.3.9 now supplies the exact residual premise of the original
R₁ argument. The established Baumann bound and both action-kernel cases
therefore exclude a solvable escaping centralizer in the covered row.
Combining this with the proved ordinary recognition and covered nonsolvable
reduction gives the original symplectic conclusion from the named earlier
structural, module, odd-normalizer and independent MS source inputs.

No local kernel, normalizer, residual selection, fusion or final recognition
premise remains. The earlier source inputs must still be discharged to
obtain unconditional 13.4.1. NaturalSixConsumer applies this implication
to remove the fixed-space premise in the original 13.5 preparation.
Source: Aschbacher--Smith 13.4.1 and 13.4.8--17, pp.896,904--915.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable Nonsolvable
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The covered row admits no solvable escaping centralizer of an original
nonfixed omega vector. The 13.3.9 premise of the R₁ argument is discharged. -/
theorem covered_solvable_escape_impossible
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G))) : False := by
  obtain ⟨Y,hYH,hnY,hYM,hp,_,hY0,_,_,hbad⟩ :=
    covered_solvable_residual_obstruction h₀ h structural D m hc z hz hzL hout hsolv
  rcases covered_point_residual h structural D m hc.2.1 z hz hzL hout hYH hnY hYM hp with
    hb | ⟨he,hcard⟩
  · exact hY0 hb
  · exact hbad.elim (fun hh => hh he) (fun hh => hh hcard)

/-- Original fixed-module recognition with the remaining covered residual
branch discharged. Only the named earlier structural/module and independent
MS inputs remain; there is no local kernel, residual or recognition callback. -/
theorem fixed_module_recognition_of_earlier_sources
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3) : ClassicalGroup.IsPSp G 3 2 := by
  rcases fixed_module_recognition_or_solvable_cover hl h₀ D hfixed structural modules earlier
      h1332 fixed five covered h13316 with hr | ⟨hc,z,_,hz,hzL,hout,hs⟩
  · exact hr
  · have hstar := Section03.Noncentrality.source1332_faithful_maximal
      h₀.qtke T h1332 h₀.local_component
    have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
      h₀.hypothesis1311.hypothesis1223
        ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
          h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
    obtain ⟨m⟩ := coreMarking_of_original_fixed h₀ h D fixed hfixed
    exact (covered_solvable_escape_impossible h₀ h structural D m hc z hz hzL hout hs).elim

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
