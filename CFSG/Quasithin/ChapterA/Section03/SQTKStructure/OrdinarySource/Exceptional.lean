module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Basic
public import Theory.SpecificGroups.Rudvalis.Multiplier.OddPrimary
public import Theory.Mathieu.M24.ValueBoundParabolics.CentralCover
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.Source
/-!
# Exceptional ordinary components in A.3.6

The odd-primary calculations for M₂₄ and Ru kill the source center when
the component has trivial two-core. Compatible Parrott lifts give the
actual Tits model. Each case concludes every common A.3.6 clause.

Source: Aschbacher–Smith A.3.6 and I.1.3, printed pp.43–45, 407.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
open Chapter1.Section02 Chapter1.Section02.LocalModels

private def modelEquivOfCenterBot {L S : Type*} [Group L] [Group S]
    (e : L ⧸ center L ≃* S) (hz : center L = ⊥) : L ≃* S :=
  QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans e)

/-- The complete M₂₄ ordinary-component branch of A.3.6. -/
theorem a36_m24 {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* Sporadic.Mathieu.M24) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup Sporadic.Mathieu.M24 := e.symm.isSimpleGroup
  let j := modelEquivOfCenterBot e
    (Sporadic.Mathieu.M24ValueBoundParabolics.center_eq_bot_of_twoCore_eq_bot hcore e)
  let : IsSimpleGroup L := j.isSimpleGroup
  exact simple_conclusion L hL (.sporadic .m24 (by intro h; cases h) ⟨j⟩)

/-- Only the proved odd-primary exclusion is needed for the Rudvalis case;
no exact two-primary multiplier is used. -/
theorem a36_ru {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* Rudvalis.Model) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  have hz : center L = ⊥ := by
    apply bot_unique
    rw [← hcore]
    exact le_sSup ⟨inferInstance, Rudvalis.Multiplier.source_center_isPGroup ⟨e⟩⟩
  let j := modelEquivOfCenterBot e hz
  let : IsSimpleGroup L := j.isSimpleGroup
  exact simple_conclusion L hL (.sporadic .ru (by intro h; cases h) ⟨j⟩)

/-- Compatible Parrott generator lifts give the actual Tits source branch. -/
theorem a36_tits {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* Tits.ParrottGroup) : A36Conclusion L := by
  let : Finite Tits.ParrottGroup := Finite.of_equiv _ e.toEquiv
  apply conclusion_of_universal_two_kernel L hL hcore e
  · rw [Tits.CentralCoverLifting.CompatibleGenerators.universalProjection_ker_eq_bot]
    exact IsPGroup.of_card (n := 0) (by simp)
  · intro j
    exact .rank_two (.tits ⟨j⟩)
end CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
