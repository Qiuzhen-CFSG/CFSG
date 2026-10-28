module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.CompletionEquality
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.Recognition
/-!
# Original ordinary U₄(2) completion recognition

The faithful completion M₀→M retains the source long-root centralizer
bound and the plane-root normalizer equality. The complete involution
catalogue, the F.4.42 short-root argument and Thompson's formula prove
|M₀|=|M|=25,920. Thus the original embedding is onto. Applying the proved
small-completion recognition and transporting through this same embedding
identifies both actual endpoint ranges with the native unitary parabolics.

This closes the ordinary U₄(2) branch of Aschbacher–Smith F.4.31 and
F.4.44, printed pp.290–296. The conclusion is the source quasiequivalence
of endpoint ranges. The graph extension and exceptional L₄(3) conclusion
of F.5 are separate branches.
-/

open Subgroup
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.OrdinaryRecognition
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open CFSG.Quasithin.ChapterF.UnitaryTwo
open CompletionEquality
local notation "hn" => Nat.le_refl 1
local notation "P" => pointParabolic 1 hn
local notation "R" => planeParabolic 1 hn
local notation "M" => ProjectiveGroup 1 hn
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
  (amalgam 1 hn) (G := G0)) (i : G0 →* G)

theorem source_ordinary_recognition
    (hi : Function.Injective i)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range)
    (z : P) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range) :
    ∃ d : G ≃* M, (i.comp c.left).range.map d.toMonoidHom = P ∧
      (i.comp c.right).range.map d.toMonoidHom = R := by
  let : Finite G0 := Finite.of_injective i hi
  obtain ⟨e,hel,her⟩ := CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Completion.exists_parabolic_preserving_equiv c
    (completion_order c i hi hnorm z hz hzroot hc)
  let q := sourceEmbeddingEquiv c i hi hnorm z hz hzroot hc
  let d := q.symm.trans e
  have he (x : G0) : d (i x) = e x := by
    change e (q.symm (i x)) = e x
    rw [← sourceEmbeddingEquiv_apply c i hi hnorm z hz hzroot hc x]
    exact congrArg e (q.symm_apply_apply x)
  have hl : d.toMonoidHom.comp (i.comp c.left) = e.toMonoidHom.comp c.left := by
    apply MonoidHom.ext
    intro x
    exact he (c.left x)
  have hr : d.toMonoidHom.comp (i.comp c.right) = e.toMonoidHom.comp c.right := by
    apply MonoidHom.ext
    intro x
    exact he (c.right x)
  refine ⟨d,?_,?_⟩
  · rw [MonoidHom.map_range,hl,MonoidHom.range_comp]
    exact hel
  · rw [MonoidHom.map_range,hr,MonoidHom.range_comp]
    exact her
/-- The literal source formulation M₀≤M: M₀=M and the original parabolic
images identify with the model endpoints. All order, involution-catalogue,
geometry and recognition premises have been discharged internally. -/
theorem subgroup_completion_recognition
    (M0 : Subgroup G)
    (d : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion (amalgam 1 hn) (G := M0))
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage d M0.subtype : Set G) =
      (M0.subtype.comp d.right).range)
    (z : P) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({(d.left z).val} : Set G) ≤ (M0.subtype.comp d.left).range) :
    M0 = ⊤ ∧ ∃ e : G ≃* M,
      (M0.subtype.comp d.left).range.map e.toMonoidHom = P ∧
      (M0.subtype.comp d.right).range.map e.toMonoidHom = R := by
  constructor
  · rw [← M0.range_subtype]
    exact MonoidHom.range_eq_top.mpr
      (source_embedding_surjective d M0.subtype M0.subtype_injective hnorm z hz hzroot hc)
  · exact source_ordinary_recognition d M0.subtype M0.subtype_injective hnorm z hz hzroot hc

end CFSG.Quasithin.ChapterF.UnitaryTwo.OrdinaryRecognition
