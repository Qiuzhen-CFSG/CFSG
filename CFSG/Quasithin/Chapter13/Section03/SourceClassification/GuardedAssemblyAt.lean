module

public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceClassification.OriginalAlternatingFiveFromRowsAt
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality

/-!
# Guarded 13.3.2 assembly at one ambient group

The Chapter 13 consumers use three earlier-source outputs on the same
`G,T`: the faithful-family normality/catalogue, the fixed-space clause and
the alternating-five marking.  The first is supplied by the guarded Chapter
12 structural adapter; the latter two are the checked row adapters.  This
module only packages those applications and keeps every genuine source
premise explicit.

Source: Aschbacher--Smith 12.2.2 and 13.3.2, printed pp.795 and 884--885.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceClassification
open Chapter12.Section02
open Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Chapter14.Section03.FaithfulSource
open Chapter13.Section03.Noncentrality.SupercriticalSource
open Chapter13.Section03.SourceCompletion

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G}

/-- The exact same-ambient 13.3.2 package needed by later source consumers.
All three fields retain the original `G,T,L` and literal chosen-module maps;
no universal structural or module theorem is manufactured here. -/
theorem original1332InputsAt_of_guarded_sources
    (h1331 : Hypothesis1331 T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (quasisimple : ∀ I : Subgroup G, FaithfulMaximalLocal T I →
      IsQuasisimple (I ⧸ pCore 2 I))
    (models : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      MidSizeModel (Chapter1.XiQuotient I))
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (exits : ∀ K : Subgroup G, ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃*
        alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H)) :
    Source1332OneTwo T ∧
      OriginalFixedModule1332At T L ∧
      OriginalAlternatingFiveModules1332At T L := by
  have source : Source1332OneTwo T :=
    Chapter12.Section02.SourceAssembly.At.source1332OneTwo_of_maximal_models
      h1331.hypothesis1311 quasisimple models structural
  have fixed : OriginalFixedModule1332At T L :=
    originalFixedModule1332At_of_guarded_source h1331 hmany quasisimple models
      structural modules exits
  have five : OriginalAlternatingFiveModules1332At T L :=
    originalAlternatingFiveModules1332At_of_module_rows quasisimple models modules
  exact ⟨source, fixed, five⟩

end CFSG.Quasithin.Chapter13.Section03.SourceClassification
