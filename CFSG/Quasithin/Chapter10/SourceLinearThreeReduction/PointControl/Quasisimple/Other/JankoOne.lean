module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.CentralImage
public import Theory.SpecificGroups.Janko1.PerfectSubgroupCore

/-!
# Excluding the actual J₁ containing carrier

The image of L is perfect. Every perfect subgroup of the native J₁ model
has central two-core, by its Sylow order eight. This contradicts the
noncentral core center forced by the original moved module. No sixteen-
element bound, A₅ quotient, or irreducibility assumption is used.

Source: Aschbacher--Smith A.3.12 and 10.2.9, pp.47--48,750--751.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
variable {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include c
/-- The literal local image excludes J₁ as a containing central quotient. -/
 theorem not_jankoOne (e : (I ⧸ center I) ≃* Janko1.Model) : False := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center I))
  let B := (L.subgroupOf I).map q
  let k : L ≃* L.subgroupOf I := (subgroupOfEquivOfLe c.strict.le).symm
  let f : L →* B := (q.subgroupMap (L.subgroupOf I)).comp k.toMonoidHom
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := f)
    ((q.subgroupMap_surjective _).comp k.surjective)
  apply marked_core_center_not_central D c.strict.le e
  rintro _ ⟨z,hz,rfl⟩
  exact Janko1.perfect_subgroup_pCore_two_le_center B z.property

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
