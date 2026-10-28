module
public import Theory.SpecificGroups.PSL3Two.PerfectCentralCover
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryNonabelian

/-!
# Lifting the original binary star marking through the two-core

The intrinsic component quotient is quasisimple. Its surjection to the
marked SL₃(2) star group is therefore a perfect central cover. The quotient
has trivial two-core, so cyclic odd-Sylow transfer removes its kernel.
The resulting marking retains the original projection and supplies the
literal binary MS input used by15.3.31.

Source: Aschbacher–Smith C.1.31 and15.3.31, printed pp.135,1132.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.CentralCover
  SmallExtension.CentralCover.LinearThree
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

/-- The actual binary star marking lifts to the full intrinsic two-core
quotient, with its original projection retained. -/
theorem source_binary_quotient_marking
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (m : Parabolics.RankTwoParabolicMarking d I c.L SL Parabolics.linearThreeParabolic) :
    ∃ e : (c.L ⧸ pCore 2 c.L) ≃* SL, ∀ l : c.L,
      e (QuotientGroup.mk' (pCore 2 c.L) l) = m.equiv (componentMap d c l) := by
  let q := QuotientGroup.lift (pCore 2 c.L) (componentMap d c)
    (core_le_componentMap_ker d c
      (component_core_centralizes_span d c s.normal s.sylow s.sylow_eq))
  have hq : Function.Surjective q :=
    QuotientGroup.lift_surjective_of_surjective _ _ (componentMap_surjective d c) _
  let := c.core_quotient_quasisimple
  let : Nontrivial (d.starImage I c.L) :=
    (nontrivial_iff_ne_bot _).mpr (component_star_ne_bot d c)
  have hk : q.ker = center (c.L ⧸ pCore 2 c.L) :=
    MarkedMS.ker_eq_center_of_quasisimple q hq
      (MarkedMS.marked_star_center d c (.linearThree m))
  let f : PerfectCentralCovering.Cover (c.L ⧸ pCore 2 c.L) SL := {
    toMonoidHom := m.equiv.toMonoidHom.comp q
    surjective := m.equiv.surjective.comp hq
    isPerfect := inferInstance
    ker_le_center := by
      intro x hx
      apply hk.le
      exact m.equiv.map_eq_one_iff.mp hx }
  refine ⟨Matrix.PSL3Two.centralCoverEquiv f (pCore_quotient_pCore_eq_bot 2),?_⟩
  intro l
  rw [Matrix.PSL3Two.centralCoverEquiv_apply]
  rfl

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
