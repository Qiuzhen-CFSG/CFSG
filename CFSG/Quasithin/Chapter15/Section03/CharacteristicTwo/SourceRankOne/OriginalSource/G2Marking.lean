module
public import Theory.SpecificGroups.G2Even.MarkedCover
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryNonabelian

/-!
# The original derived G₂ star marking on the intrinsic quotient

The component quotient is quasisimple, and the kernel of its map to the
marked star group is central. The proved binary derived G₂ covering result
makes that kernel a two-group. Its two-core is trivial, so the marking lifts
to the full intrinsic quotient with the original projection retained.

This discharges quotient lifting in the G₂ branch of 15.3.31 independently
of the remaining MS whole-core reconstruction.
Source: Aschbacher–Smith 15.3.26–31, printed pp. 1130–1132.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.CentralCover

variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

/-- The actual derived G₂ star marking lifts to the full intrinsic two-core
quotient, with its original projection retained. -/
theorem source_g2_quotient_marking
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (m : Parabolics.RankTwoParabolicMarking d I c.L
      (commutator (Atlas.G2.Model (ZMod 2))) Parabolics.g2DerivedParabolic) :
    ∃ e : (c.L ⧸ pCore 2 c.L) ≃* commutator (Atlas.G2.Model (ZMod 2)), ∀ l : c.L,
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
      (MarkedMS.marked_star_center d c (.g2Derived m))
  let f : PerfectCentralCovering.Cover (c.L ⧸ pCore 2 c.L) (commutator (Atlas.G2.Model (ZMod 2))) := {
    toMonoidHom := m.equiv.toMonoidHom.comp q
    surjective := m.equiv.surjective.comp hq
    isPerfect := inferInstance
    ker_le_center := by
      intro x hx
      apply hk.le
      exact m.equiv.map_eq_one_iff.mp hx }
  have hk2 := BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.binaryDerived_kernel_isTwoGroup f
  have hfi : Function.Injective f.toMonoidHom := by
    apply f.toMonoidHom.ker_eq_bot_iff.mp
    apply bot_unique
    exact (show f.toMonoidHom.ker ≤ pCore 2 (c.L ⧸ pCore 2 c.L) from
      le_sSup ⟨inferInstance, hk2⟩).trans_eq (pCore_quotient_pCore_eq_bot 2)
  exact ⟨MulEquiv.ofBijective f.toMonoidHom ⟨hfi, f.surjective⟩, fun _ => rfl⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
