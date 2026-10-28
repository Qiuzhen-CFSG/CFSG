module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Extension
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityLongCentralizer

/-!
# Common centralizers for the marked triality root pair

The original pair stabilizer lies in the overlap of the original two
normalizers. The proof uses the full marked long-root centralizer and the
short-root extension containment in the same extension, retaining the given
reversed comparison and root equations.

Source: Aschbacher--Smith, F.4.42, printed pp.294--295, and 5.3.3, p.659
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.LeviCommutators
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.TrialityNonbinary
variable {G : Type*} [Group G] [Finite G]

/-- The stabilizer of the original marked commuting pair belongs to the
original whole-normalizer overlap. -/
theorem Preparation.triality_short_long_common_centralizer
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    let P := binaryParameters m hm
    let t : G := (e.right.symm (TrialityCompletionFusion.shortElement P rfl)).val
    let z : G := (e.right.symm (TrialityCompletionFusion.longElement P rfl)).val
    centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  let P := binaryParameters m hm
  let a := d.trialityNormalizerMarking h hH hp m hm e
  let t : G := (e.right.symm (TrialityCompletionFusion.shortElement P rfl)).val
  let z : G := (e.right.symm (TrialityCompletionFusion.longElement P rfl)).val
  obtain ⟨hz,k,hk,hkz⟩ := d.triality_long_centralizer_full_marked h hH hp m hm e a
  have ht : t ∈ normalizer (residual H : Set G) :=
    a.right_le (e.right.symm (TrialityCompletionFusion.shortElement P rfl)).property
  let tN : normalizer (residual H : Set G) := ⟨t,ht⟩
  have htm : (a.comparison.right tN).val = MulAut.conj (short P rfl 2 1) := by
    change (a.comparison.right (inclusion a.right_le
      (e.right.symm (TrialityCompletionFusion.shortElement P rfl)))).val = _
    rw [a.right_marked,e.right.apply_symm_apply]
    rfl
  have hm2 := (d.triality_local_structure h hH.1.1.2 hp m hm e).2.1
  change centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) ≤
    normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  intro g hg
  let gN : normalizer (residual H : Set G) := ⟨g,hz hg.2⟩
  have hc : inclusion a.extension.left_le (a.comparison.right gN) ∈
      centralizer ({a.extension.baseHom (short P rfl 2 1)} : Set a.extension.carrier) := by
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    have he := congrArg (fun x => (a.comparison.right x).val)
      (show gN * tN = tN * gN from Subtype.ext (mem_centralizer_singleton_iff.mp hg.1))
    simp only [map_mul] at he
    change (a.comparison.right gN).val * (a.comparison.right tN).val =
      (a.comparison.right tN).val * (a.comparison.right gN).val at he
    rw [htm] at he
    exact he
  have hright := TrialityShortExtension.short_centralizer_le_right hm2 a.extension 1 one_ne_zero hc
  let b : a.extension.middle := ⟨(a.comparison.right gN).val,(a.comparison.right gN).property,hright⟩
  have he : (a.comparison.middle.symm b).val = g := by
    have hh := congrArg Subtype.val (a.comparison.symm.right_commutes b)
    change (a.comparison.right.symm ⟨b.val,b.property.1⟩).val = _ at hh
    have hr : (⟨b.val,b.property.1⟩ : a.extension.left) = a.comparison.right gN := Subtype.ext rfl
    rw [hr,a.comparison.right.symm_apply_apply] at hh
    exact hh.symm
  exact he ▸ (a.comparison.middle.symm b).property
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
