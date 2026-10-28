module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.RelativeOvergroup
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.PlaneIndex

/-!
# The actual source overgroup action

The proved marked-action surjectivity discharges the final premise of the
literal relative-cover transport. No Sylow or fixed-model hypothesis is used.

Source: Aschbacher–Smith 15.3.38, printed pp.1136–1137.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel Matrix.PSL3Four.ExtendedCentralizer
variable {G : Type*} [Group G] [Finite G]
variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}

/-- The complete marked source overgroup, with its full projective action. -/
def LocalResult.extendedOvergroup (s : SourceInputs d) (r : LocalResult d I L)
    (h : Setup d I L) (e : PSL(3,r.marking.F) ≃* Matrix.PSL3Four.PSL) :
    letI : (L.subgroupOf I).Normal := r.cover.normal
    Overgroup (L.subgroupOf I) :=
  r.extendedOvergroupOfSurjective s h e (r.marked_action_surjective s h)

/-- The actual source overgroup uses the original relative cover. -/
@[simp] theorem LocalResult.extendedOvergroup_cover (s : SourceInputs d)
    (r : LocalResult d I L) (h : Setup d I L)
    (e : PSL(3,r.marking.F) ≃* Matrix.PSL3Four.PSL) :
    letI : (L.subgroupOf I).Normal := r.cover.normal
    (r.extendedOvergroup s h e).cover = r.relativeFourCover h e := by
  exact r.extendedOvergroupOfSurjective_cover s h e (r.marked_action_surjective s h)

/-- The full source overgroup action, in the caller's arbitrary projective marking. -/
theorem LocalResult.extendedOvergroup_projectiveAction_eq (s : SourceInputs d)
    (r : LocalResult d I L) (h : Setup d I L)
    (e : PSL(3,r.marking.F) ≃* Matrix.PSL3Four.PSL) :
    letI : (L.subgroupOf I).Normal := r.cover.normal
    projectiveAction (L.subgroupOf I) (r.extendedOvergroup s h e).cover =
      (MulAut.congr e).toMonoidHom.comp
        ((markedAction r.marking).comp (inclusion (h.normalizes_component s.earlier))) := by
  let : (L.subgroupOf I).Normal := r.cover.normal
  rw [r.extendedOvergroup_cover s h e]
  exact r.relative_projectiveAction_eq s h e

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
end
