module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.Models
public import Theory.Representation.BinaryOffender.NormalizerImage
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PerfectCentralizerLift

/-!
# Faithful-image reduction for the classical full-normalizer problem

The source B.1.11 section may have a central action kernel. Its image is
nevertheless nontrivial and quasisimple, and perfect centralizer lifting
identifies the two simple central quotients by an actual equivalence.
The binary action, full normalizer and offender are retained literally.

The last theorem applies this reduction to the complete parameterized
classical catalogue used in B.1.13 (Aschbacher–Smith, printed pp.73–74).
It supplies inputs for the cross-characteristic representation analysis;
it does not assert that analysis or the quotient classification.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal
universe u v
variable {L : Type u} {W : Type v} [Group L] [IsQuasisimple L]
  [AddCommGroup W] [Module (ZMod 2) W]
  (σ : Representation (ZMod 2) L W)

/-- A central action kernel cannot kill a quasisimple group. -/
theorem actionImage_nontrivial (hk : σ.ker ≤ center L) : Nontrivial (actionImage σ) := by
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  by_contra hn
  let : Subsingleton (actionImage σ) := not_nontrivial_iff_subsingleton.mp hn
  have hc : center L = ⊤ := by
    apply top_unique
    intro l _
    apply hk
    have h := congrArg (imageRepresentation σ) (Subsingleton.elim (actionHom σ l) 1)
    change σ l = 1
    simpa only [imageRepresentation_actionHom, map_one] using h
  exact Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp hc)

/-- The actual image is quasisimple without assuming the original action faithful. -/
theorem actionImage_quasisimple (hk : σ.ker ≤ center L) : IsQuasisimple (actionImage σ) := by
  let := actionImage_nontrivial σ hk
  exact IsQuasisimple.of_surjective (actionHom σ) σ.asGroupHom.rangeRestrict_surjective

/-- Perfect centralizer lifting identifies the two simple central quotients. -/
noncomputable def actionImage_quotientCenterEquiv (hk : σ.ker ≤ center L) :
    L ⧸ center L ≃* actionImage σ ⧸ center (actionImage σ) := by
  let f := actionHom σ
  have hf : Function.Surjective f := σ.asGroupHom.rangeRestrict_surjective
  have hkf : f.ker ≤ center L := by
    intro l hl
    apply hk
    change σ l = 1
    simpa only [f, imageRepresentation_actionHom, map_one] using
      congrArg (imageRepresentation σ) (show f l = 1 from hl)
  have hc : (center (actionImage σ)).comap f = center L := by
    have he := comap_centralizer_map_eq_of_perfect f (⊤ : Subgroup L)
      (by simpa only [coe_top, centralizer_univ] using hkf)
    simpa only [Subgroup.map_top_of_surjective f hf, coe_top, centralizer_univ] using he
  let q := (QuotientGroup.mk' (center (actionImage σ))).comp f
  have hq : q.ker = center L := by
    rw [show q.ker = (center (actionImage σ)).comap f by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']]
    exact hc
  exact (QuotientGroup.quotientMulEquivOfEq hq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q ((QuotientGroup.mk'_surjective _).comp hf))

/-- All six concrete model witnesses, including their exact parameter,
pass to the faithful image's simple quotient. -/
theorem actionImage_classicalAt (hk : σ.ker ≤ center L) {q : ℕ}
    (hm : IsClassicalAt (L ⧸ center L) q) :
    IsClassicalAt (actionImage σ ⧸ center (actionImage σ)) q := by
  let e := (actionImage_quotientCenterEquiv σ hk).symm
  cases hm with
  | linear n hp hi => exact .linear n hp (hi.of_mulEquiv e)
  | unitary n hp hi => exact .unitary n hp (hi.of_mulEquiv e)
  | symplectic r hp hi => exact .symplectic r hp (hi.of_mulEquiv e)
  | orthogonalPlus r hp hi => exact .orthogonalPlus r hp (hi.of_mulEquiv e)
  | orthogonalOdd r hp hi => exact .orthogonalOdd r hp (hi.of_mulEquiv e)
  | orthogonalMinus r hp hi => exact .orthogonalMinus r hp (hi.of_mulEquiv e)

/-- Apply the reductions to the source classical input. The output keeps an
actual offender in the full normalizer, with faithful conjugation on the image. -/
theorem faithful_classical_image (hk : σ.ker ≤ center L)
    (hi : Representation.IsIrreducible σ)
    (hff : IsFFModule (normalizerRepresentation σ)) {q : ℕ}
    (hm : IsClassicalAt (L ⧸ center L) q) :
    IsQuasisimple (actionImage σ) ∧
    Representation.IsIrreducible (imageRepresentation σ) ∧
    Function.Injective (imageRepresentation σ) ∧
    IsClassicalAt (actionImage σ ⧸ center (actionImage σ)) q ∧
    ∃ A : Subgroup (linearNormalizer (imageRepresentation σ)),
      IsOffender (normalizerRepresentation (imageRepresentation σ)) A ∧
      Function.Injective
        ((actionImage (imageRepresentation σ)).normalizerMonoidHom.comp A.subtype) := by
  have hi' := imageRepresentation_isIrreducible σ hi
  have hf' := (isFFModule_normalizer_imageRepresentation_iff σ).mpr hff
  exact ⟨actionImage_quasisimple σ hk, hi', imageRepresentation_injective σ,
    actionImage_classicalAt σ hk hm,
    exists_offender_with_injective_conjugation (imageRepresentation σ) hi' hf'⟩

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal
