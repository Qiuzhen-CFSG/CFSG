module
public import CFSG.Quasithin.Chapter5.Section03UnitaryNativeLift.Geometry
public import Theory.GroupTheory.Amalgam.AutomorphismTransport

/-!
# Exact extension of native unitary amalgam automorphisms

Compare the pure native completion with its twist by the supplied amalgam
automorphism. Both have the native carrier and satisfy the fourth-power
relation. Their paired completion has girth eight and a transitive action
on five-paths, so the matching involutions make both projections bijective.
Conjugating the resulting automorphism back to the native projective group
preserves each supplied endpoint map pointwise.

This is a sufficient intrinsic realization step for Aschbacher–Smith 5.3.2
(pp.658–659), using F.4.8–10,16–17 (pp.278–283). No source join is identified,
and no exact-marking conclusion for an arbitrary outer extension is assumed.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter5.UnitaryNativeLift
open Subgroup Theory.GroupTheory
open ChapterF.SourceCompletion.UnitaryNonbinary

private theorem reverse_product_power {M : Type*} [Group M]
    (s t : M) (n : ℕ) (h : (t*s)^n = 1) : (s*t)^n = 1 := by
  have hh := congrArg (MulAut.conj s) h
  simpa only [map_pow, map_one, MulAut.conj_apply, mul_assoc, mul_inv_cancel, mul_one] using hh

private theorem nativeLeft_out {B M : Type*} [Group B] [Group M]
    {P Q : Subgroup B} (E : SourceExtension P Q)
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (s : P) (hs : s.val ∉ Q) : c.left (E.nativeLeft s) ∉ c.middle.range := by
  rintro ⟨d, hd⟩
  have he := congrArg Subtype.val (c.left_injective hd)
  change d.val = MulAut.conj s.val at he
  apply hs
  apply (E.conj_mem_right_iff hi s.val).mp
  rw [← he]
  exact d.property.2

private theorem nativeRight_out {B M : Type*} [Group B] [Group M]
    {P Q : Subgroup B} (E : SourceExtension P Q)
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (t : Q) (ht : t.val ∉ P) : c.right (E.nativeRight t) ∉ c.middle.range := by
  rintro ⟨d, hd⟩
  have he := congrArg Subtype.val (c.right_injective
    ((DFunLike.congr_fun c.compatible d).symm.trans hd))
  change d.val = MulAut.conj t.val at he
  apply ht
  apply (E.conj_mem_left_iff hi t.val).mp
  rw [← he]
  exact d.property.1

namespace Four
open ChapterF.GreenBook.LieModels.UnitaryFour
variable (m : ℕ) (hm : 1 ≤ m) (hmgt : 1 < m)
include hmgt

/-- The pure-carrier automorphism agrees exactly with the twisted endpoint maps. -/
theorem extension_automorphism
    (a : RankTwoAmalgam.Iso (extension m hm).amalgam (extension m hm).amalgam) :
    ∃ f : MulAut (extension m hm).carrier,
      (∀ x, f (((extension m hm).completion (parabolics_generate m hm)).left x) =
        ((extension m hm).completion (parabolics_generate m hm)).left (a.left x)) ∧
      (∀ x, f (((extension m hm).completion (parabolics_generate m hm)).right x) =
        ((extension m hm).completion (parabolics_generate m hm)).right (a.right x)) := by
  let E := extension m hm
  let c := E.completion (parabolics_generate m hm)
  let d := c.comapIso a
  have hc : c.left.range ⊓ c.right.range = c.middle.range := E.completion_overlap _
  have hd : d.left.range ⊓ d.right.range = d.middle.range := by
    simpa only [d, RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using hc
  have hp := Paired.marked_pair_overlap c d hc
  let s := E.nativeLeft (FourWeyl.point m hm)
  let t := E.nativeRight (FourWeyl.plane m hm)
  have hs : s^2 = 1 := by
    dsimp only [s]
    rw [← map_pow, FourWeyl.point_sq, map_one]
  have ht : t^2 = 1 := by
    dsimp only [t]
    rw [← map_pow, FourWeyl.plane_sq, map_one]
  obtain ⟨f, hl, hr⟩ := Paired.exists_marked_mulEquiv_of_matching_involutions c d hc hd
    (girth m hm c hc) (girth m hm d hd) (girth m hm _ hp)
    (four_completion_rootPathTransitive_five m hm E _ hp) s t hs ht
    (nativeLeft_out E (four_conj_injective m hm) c _ (point_out m hm))
    (nativeRight_out E (four_conj_injective m hm) c _ (plane_out m hm))
    (reverse_product_power _ _ 4 (fourth_eq_one m hm hmgt c hc le_rfl))
    (reverse_product_power _ _ 4 (fourth_eq_one m hm hmgt d hd le_rfl))
  exact ⟨f, hl, hr⟩

/-- Every native amalgam automorphism extends with both prescribed endpoint maps. -/
theorem native_automorphism (a : RankTwoAmalgam.Iso (amalgam m hm) (amalgam m hm)) :
    ∃ f : MulAut (ProjectiveGroup m hm),
      (∀ x : pointParabolic m hm, f x.val = (a.left x).val) ∧
      (∀ x : planeParabolic m hm, f x.val = (a.right x).val) := by
  let e := comparison m hm
  let b := RankTwoAmalgam.automorphismConjEquiv e a
  obtain ⟨f, hl, hr⟩ := extension_automorphism m hm hmgt b
  let z := Pure.baseEquiv (pointParabolic m hm) (planeParabolic m hm) (four_conj_injective m hm)
  refine ⟨z.trans (f.trans z.symm), ?_, ?_⟩
  · intro x
    apply z.injective
    change z (z.symm (f (z x.val))) = z (a.left x).val
    rw [z.apply_symm_apply]
    change f (((extension m hm).completion (parabolics_generate m hm)).left (e.left x)) =
      ((extension m hm).completion (parabolics_generate m hm)).left (e.left (a.left x))
    rw [hl]
    congr 1
    change e.left (a.left (e.left.symm (e.left x))) = _
    rw [e.left.symm_apply_apply]
  · intro x
    apply z.injective
    change z (z.symm (f (z x.val))) = z (a.right x).val
    rw [z.apply_symm_apply]
    change f (((extension m hm).completion (parabolics_generate m hm)).right (e.right x)) =
      ((extension m hm).completion (parabolics_generate m hm)).right (e.right (a.right x))
    rw [hr]
    congr 1
    change e.right (a.right (e.right.symm (e.right x))) = _
    rw [e.right.symm_apply_apply]

end Four

namespace Five
variable (U : ChapterF.GreenBook.UnitaryFive.Model 4)

/-- The pure-carrier automorphism agrees exactly with the twisted endpoint maps. -/
theorem extension_automorphism
    (a : RankTwoAmalgam.Iso (extension U).amalgam (extension U).amalgam) :
    ∃ f : MulAut (extension U).carrier,
      (∀ x, f (((extension U).completion (parabolics_generate U)).left x) =
        ((extension U).completion (parabolics_generate U)).left (a.left x)) ∧
      (∀ x, f (((extension U).completion (parabolics_generate U)).right x) =
        ((extension U).completion (parabolics_generate U)).right (a.right x)) := by
  obtain ⟨u, hu⟩ := exists_trace_parameter U
  let E := extension U
  let c := E.completion (parabolics_generate U)
  let d := c.comapIso a
  have hc : c.left.range ⊓ c.right.range = c.middle.range := E.completion_overlap _
  have hd : d.left.range ⊓ d.right.range = d.middle.range := by
    simpa only [d, RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using hc
  have hp := Paired.marked_pair_overlap c d hc
  let s := E.nativeLeft (FiveWeyl.point U u hu)
  let t := E.nativeRight (FiveWeyl.plane U u hu)
  have hs : s^2 = 1 := by
    dsimp only [s]
    rw [← map_pow, FiveWeyl.point_sq, map_one]
  have ht : t^2 = 1 := by
    dsimp only [t]
    rw [← map_pow, FiveWeyl.plane_sq, map_one]
  obtain ⟨f, hl, hr⟩ := Paired.exists_marked_mulEquiv_of_matching_involutions c d hc hd
    (girth U c hc) (girth U d hd) (girth U _ hp)
    (five_completion_rootPathTransitive_five U E _ hp) s t hs ht
    (nativeLeft_out E (five_conj_injective U) c _ (point_out U u hu))
    (nativeRight_out E (five_conj_injective U) c _ (plane_out U u hu))
    (reverse_product_power _ _ 4 (fourth_eq_one U u hu c hc le_rfl))
    (reverse_product_power _ _ 4 (fourth_eq_one U u hu d hd le_rfl))
  exact ⟨f, hl, hr⟩

/-- Every native amalgam automorphism extends with both prescribed endpoint maps. -/
theorem native_automorphism (a : RankTwoAmalgam.Iso U.amalgam U.amalgam) :
    ∃ f : MulAut (U.Carrier),
      (∀ x : U.leftParabolic, f x.val = (a.left x).val) ∧
      (∀ x : U.rightParabolic, f x.val = (a.right x).val) := by
  let e := comparison U
  let b := RankTwoAmalgam.automorphismConjEquiv e a
  obtain ⟨f, hl, hr⟩ := extension_automorphism U b
  let z := Pure.baseEquiv U.leftParabolic U.rightParabolic (five_conj_injective U)
  refine ⟨z.trans (f.trans z.symm), ?_, ?_⟩
  · intro x
    apply z.injective
    change z (z.symm (f (z x.val))) = z (a.left x).val
    rw [z.apply_symm_apply]
    change f (((extension U).completion (parabolics_generate U)).left (e.left x)) =
      ((extension U).completion (parabolics_generate U)).left (e.left (a.left x))
    rw [hl]
    congr 1
    change e.left (a.left (e.left.symm (e.left x))) = _
    rw [e.left.symm_apply_apply]
  · intro x
    apply z.injective
    change z (z.symm (f (z x.val))) = z (a.right x).val
    rw [z.apply_symm_apply]
    change f (((extension U).completion (parabolics_generate U)).right (e.right x)) =
      ((extension U).completion (parabolics_generate U)).right (e.right (a.right x))
    rw [hr]
    congr 1
    change e.right (a.right (e.right.symm (e.right x))) = _
    rw [e.right.symm_apply_apply]

end Five

end CFSG.Quasithin.Chapter5.UnitaryNativeLift
