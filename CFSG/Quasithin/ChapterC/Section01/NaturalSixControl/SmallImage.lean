module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.FullImage
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.FixedGeometry

/-!
# The small-image alternatives of the S6 point case

If the original Thompson image is trivial, B.2.10 makes the Baumann subgroup
normal. If it is nontrivial but contained in the point transposition, the
pointwise fixer of the natural fixed hyperplane forces the Baumann image to
be exactly that transposition. The proved natural-six C.1.24(c) theorem then
gives the characteristic-normal or A6-block alternative on the original
component. The chosen quotient relabeling does not change the source point
parabolic or its Baumann subgroup.

Source: Aschbacher--Smith C.1.37, printed p.142, cases (i)--(ii).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.NaturalSixControl
open Subgroup Stellmacher
open scoped IsMulCommutative
open ChapterB ChapterB.BaumannArgument
open Representation.BinaryOffender
open ChapterB.Offenders.Six
universe u
variable {K : Type u} [Group K] [Finite K]
variable {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
namespace SourceData
variable (d : SourceData L V T)
include d

theorem baumann_image_eq_last
    (hne : (elementaryAbelianMaxJ d.R).map d.q0 ≠ ⊥)
    (hle : (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) : d.B.map d.q0 = last := by
  let := d.elementary
  have hj : ¬ elementaryAbelianMaxJ d.R ≤ d.q0.ker :=
    fun h => hne ((Subgroup.map_eq_bot_iff _).mpr h)
  apply (thompson_baumann_image_of_unique_maximum_image V d.R d.q0 last
    d.module_le_radical hj ?_ ?_).2
  · intro A hA hn
    have ha : A.map d.q0 ≤ Model.E := by
      apply map_le_iff_le_comap.mpr
      exact hA.1.trans_eq d.R_eq_comap
    have hb : IsBestOffender Model.rho (A.map d.q0) :=
      (d.canonicalAction.bestOffender_iff _).mp
        (Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
          V d.q0 d.q0_onto d.canonicalAction.kernel_centralizer d.R A d.module_le_radical hA hn)
    apply le_antisymm ((map_mono (le_sSup hA)).trans hle)
    apply (closure_le _).mpr
    rintro x rfl
    exact Model.best_contains_swap ha hb
  · rw [d.R_eq_comap]
    exact d.canonicalAction.last_fixed_fixer_image_le

/-- The literal characteristic-or-block conclusion in both small-image cases. -/
theorem characteristic_or_block_of_small_thompson_image
    (hle : (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) :
    (∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map d.B.subtype).Normal) ∨ IsAlternatingBlock L 6 := by
  by_cases hz : (elementaryAbelianMaxJ d.R).map d.q0 = ⊥
  · left
    apply d.characteristic_of_thompson_image_bot
    have hker := (Subgroup.map_eq_bot_iff _).mp hz
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [d.ker_eq]
    exact hker.trans_eq d.q0_kernel
  · let d0 : SourceData L V T := {d with
      q := d.q0
      onto := d.q0_onto
      ker_eq := d.q0_kernel
      image_component := d.q0_image_component
      eV := d.e0
      action := d.e0_action }
    have heP : d0.P = d.P := rfl
    have hB : d0.B.map d0.q = zpowers (ChapterB.Offenders.pairSwap 6 2) := by
      rw [zpowers_eq_closure]
      exact d.baumann_image_eq_last hz hle
    have hr : (ChapterB.Offenders.pairSwap 6 2).IsSwap := by
      exact ⟨4,5,by decide,by decide⟩
    exact d0.characteristic_or_block_of_baumann_image_swap _ hr hB

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl
