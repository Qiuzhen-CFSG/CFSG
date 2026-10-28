module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFiveTransport
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalUnitaryRestriction

/-!
# The original Chapter 12 U₅ marking and its native Sylow and core action

For every selected perfect R, first use the quasithin field obstruction and
residual quotient to force q=4 and the plane-first orientation. The same
original marking identifies both local Sylows, their order 2²⁰, and the exact
inner part of the source S image. The full native line Borel normalizes that
image, and the original join-core acts trivially on the line SU₃(4) quotient.

These are source-specific transport and normalized-Borel inputs for removing
the original U₅ extension in F.1.12, printed pp.263--264. They do not identify
S with T or R with O²(H). Native kernel detection, the surviving U₄ extension
restriction, broad DGS exhaustiveness, uniqueness and final GlobalExit
assembly remain obligations of their existing owners. The prepared U₅
completion is already proved in GlobalUnitaryFiveSource.Completion.
Source: Aschbacher--Smith 5.2.6, pp.650--651, and Chapter 12, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Arbitrary original U₅ parameters reduce to q=4; the common native
Sylow is the actual ambient T∩L, in both original selected factors. -/
theorem rankOne_global_original_unitaryFive_intersections
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) {q : ℕ} (hq : IsPrimePow q) (heven : Even q)
    (M : ChapterF.GreenBook.UnitaryFive.Model q) (line : Bool)
    (hi : Function.Injective (MulAut.conj : M.Carrier →* MulAut M.Carrier))
    (e : Global.OriginalUnitaryFive.Marking M line L R (Global.sourceS L H)) :
    q = 4 ∧ line = false ∧ n = 4 ∧
      Global.sourceS L H ⊓ R = (T : Subgroup G) ⊓ L ∧
      Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) = 2^20 := by
  let hinput := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hq4 := Global.Preparation.original_unitaryFive_marked_field hinput hq heven M line hi e
  subst q
  have ho := d.original_unitaryFive_marked_orientation hinput hH.1.1.2 hp M line e
  subst line
  have hn4 := (d.original_unitaryFive_marked_parameters hinput hH.1.1.2 hp M false e).1
  have hs := d.original_unitaryFive_intersections hinput hH.1.1.2 hp M e
  have hc := (d.original_unitaryFive_intersections_card hinput hH.1.1.2 hp M e).1
  rw [d.left_intersection] at hc
  exact ⟨rfl,rfl,hn4,hs.symm.trans d.left_intersection,hc⟩

/-- The same original marking supplies the exact inner source image and
normalized native Borel; every source join-core element has trivial action
on the actual SU₃(4) residual quotient. -/
theorem rankOne_global_original_unitaryFive_core_transport
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) (M : ChapterF.GreenBook.UnitaryFive.Model 4)
    (e : Global.OriginalUnitaryFive.Marking M false L R (Global.sourceS L H)) :
    e.sylowHom.range ⊓ MulAut.innerSubgroup M.Carrier = M.flagTwoSubgroup.map MulAut.conj ∧
    (M.leftLocalImage ⊓ normalizer (M.flagTwoSubgroup : Set M.Carrier)).map MulAut.conj ≤
      normalizer (e.sylowHom.range : Set _) ∧
    ∀ g : (R ⊔ Global.sourceS L H).pCoreIn 2,
      ∃ s : Global.sourceS L H, s.val = g.val ∧
        Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightQuotientAction
          M.rightParabolic M.leftParabolic
          (e.sylowFlagHom (Theory.SpecificGroups.UnitaryFive.SmallCompletion.conj_injective
            M.form M.local_field_card M.conjugation M.matrix) s) = 1 := by
  let hinput := D.rankOne_generic_input_of_many h hmany hn hpsl
  refine ⟨d.original_unitaryFive_source_inner hinput hH.1.1.2 hp M e,
    d.original_unitaryFive_borel_normalizes hinput hH.1.1.2 hp M e,?_⟩
  intro g
  let s : Global.sourceS L H := ⟨g.val,d.original_right_core_le_sourceS hinput hH.1.1.2 g.property⟩
  exact ⟨s,rfl,d.original_unitaryFive_core_quotient_action hinput hH.1.1.2 hp M e s g.property⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
