module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperModels
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperSeven
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePointCoreGeometry

/-!
# Original local maximality in the normal A₆ branch

The complete source model reduction leaves the original maximal local
component or a proper upper component with A₇ quotient. In the latter
case the actual small binary module and H¹ calculations give O₂(LT)=V.
The original characteristic-two centralizer calculation then excludes
seven from |Gz|, while the upper A₇ fixed-vector argument puts seven
in that same literal order. Thus the proper upper case is impossible.

The final theorem constructs Hypothesis1221 for the original L using
its inherited faithful-local data. It discharges the maximality input
used in the exceptional quotient and normalizer argument of13.5.15;
no upper-model, cohomology, centralizer or maximality premise is added.
The specialization retains all original normal A₆ branch hypotheses.
Source: Aschbacher–Smith13.3.2 and13.5.15, pp.884–885,920–921.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.Original
open Section08.SourceCompletion Chapter13.Section05.NormalBranch
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

/-- The actual normal A₆ setup excludes every A₇ maximal upper component. -/
theorem no_seven_upper {I : Subgroup G}
    (hI : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T I)
    (hLI : D.L ≤ I) (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) : False :=
  SourcePointCoreGeometry.seven_not_dvd_point_group_card d h e hseed hn hU
    (UpperAction.original_core_eq_module_of_seven d h e hseed hn hU hI hLI eI)
    (UpperAction.seven_dvd_point_centralizer d h e hseed hn hU hI hLI eI)

/-- Original13.3.2 maximality specialized to the unchanged normal A₆ consumer. -/
theorem original_maximal : D.L ∈ Chapter1.LStar G (D.T : Subgroup G) := by
  rcases UpperModels.original_maximal_or_seven_overgroup d h e hseed hn hU with hm | hx
  · exact hm
  · obtain ⟨I,hLI,hI,_,hseven⟩ := hx
    obtain ⟨eI⟩ := hseven
    exact (no_seven_upper d h e hseed hn hU hI hLI.le eI).elim

/-- Supply the exact earlier-source hypothesis used by the original quotient consumer. -/
theorem original_hypothesis1221 :
    Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L := by
  have hL := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff D.T D.L).mp
    d.counterexample.local_component
  exact ⟨d.counterexample.qtke,⟨original_maximal d h e hseed hn hU,hL.2⟩,
    SixMaximality.NaturalSetup.local_overgroup_quasisimple d e hL.1 le_rfl⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.Original
