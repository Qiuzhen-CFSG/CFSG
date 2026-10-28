module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.SourceReduction.Noncommuting
public import CFSG.Quasithin.Chapter12.Section09.SourceInputs

/-!
# The full natural marking in 12.5.1

Seven-case selection gives natural coordinates on the entire original V
or an exterior marking, including the dual exterior action. The original
local, fusion, weak-closure, terminal and point-escape arguments now exclude
the latter. The surviving natural marking intertwines the original
conjugation action with the original L-to-L/O₂(L) projection, exactly as
required by Section09.NaturalModule and NaturalReduction.

The first export takes only the precise earlier source statements at the
same G,T. The universal export takes genuine universal earlier statements;
it does not infer them from guarded versions. Their existing producers
are qt-d-1222-source and qt-d-1222-modules, with final discharge retained
by qt-d-1332-source. All local exterior obligations are discharged here.

Source: Aschbacher--Smith, 12.5.1, printed pp.816--822.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Original 12.5.1, conditional only on earlier source theorems at this G,T. -/
theorem naturalModule_from_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 5 2) :
    Section09.NaturalModule D 5 := by
  rcases natural_or_exterior_of_moduleAlternatives D hL (modules L V h D) with hn | ha
  · exact hn
  · obtain ⟨a⟩ := ha
    obtain ⟨s,_⟩ := exists_sylow_marking_with_local_source h structural a
    exact (s.exterior_false_from_source h structural modules).elim

/-- Universal 12.5.1 with the genuine universal earlier inputs explicit. -/
theorem naturalReduction_from_source
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple) :
    Section09.NaturalReduction.{u} KnownSimple.IsKnownSimple 5 := by
  intro G _ _ T L V h D hL
  exact naturalModule_from_source h D (structural.at T) (modules G T) hL

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
