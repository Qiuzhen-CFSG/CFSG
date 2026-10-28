module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.Models
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.CriticalImages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.SourceThree.Bound

/-!
# Binary bad-case offender and commutator estimates

The three actual marked bad alternatives give a unique elementary offender
on every edge, with equal fixed codimension and rank and the required edge
centralizer. Comparing the two critical displacement indices makes the
opposite endpoint images offenders. Their uniqueness then gives normalization
and equality of the endpoint images modulo the initial kernel.

The completed local calculation `badCase_source33Bound` uses the literal
actor Q_t ∩ C([Z_a,Z_a']) and A = X_a ∩ Q_a'. The Frattini premise makes
Y centralize X_a, so this bound implies [Y,Z_a'] ≤ [X_a,X_a']. Together
with the critical-image comparison, it proves all four `BadCaseEstimates`
fields. The auxiliary commutator is normal in the initial edge kernel and
not normal in G_a. `critical_endpoint_choice` supplies Z(a,a') = Z_a',
its containment in X_a', and its noncontainment in Q_a by critical reversal.

These conclusions take `BadCase` explicitly; construction and eventual
exclusion of those alternatives remain with the source-classification owner.
The older action-control implication is preserved as a conditional helper.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (2.3)(c,d), (3.2)(iii)–(v), (3.3), and the initial argument of
(3.8), printed pp.857–858,863–868,877–878.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Every actual adjacent edge has the unique nontrivial elementary offender,
with equality of fixed codimension and rank and the exact edge centralizer. -/
theorem badCase_edgeOffenderUniqueness (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hbad : BadCase source) : EdgeOffenderUniqueness source :=
  Models.badCase_edgeOffenderUniqueness source geometry hb hbad

/-- The actual critical endpoint images are normalized by the initial edge
kernel and agree for all critical endpoints through that edge. -/
theorem badCase_criticalImageControl (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hbad : BadCase source) : CriticalImageControl R geometry :=
  criticalImageControl_of_edgeOffenderUniqueness source geometry hb
    (badCase_edgeOffenderUniqueness source geometry hb hbad)

/-- The binary bad alternatives establish the source-(2.3)(c,d) estimates.
Every local-action and critical-image premise is discharged here. The endpoint
witness and noncontainment are given by `critical_endpoint_choice`. -/
theorem badCaseEstimates_of_badCase (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (hbad : BadCase source) : BadCaseEstimates R geometry := by
  have hbpos : 0 < geometry.b R := by omega
  exact badCaseEstimates_of_local_bounds source geometry hb
    (badCase_source33Bound source geometry hbpos hbad)
    (badCase_criticalImageControl source geometry hbpos hbad)

/-- The BadCase branch supplies the model action control; this wrapper exposes
its source-3.3 consequence to downstream estimates. -/
theorem badCase_source33Bound_of_action_control
    (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (_hbad : BadCase source)
    (hcontrol : Source33ActionControl source geometry hb) :
    Source33Bound R geometry :=
  source33Bound_of_action_control source geometry hb hcontrol

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
