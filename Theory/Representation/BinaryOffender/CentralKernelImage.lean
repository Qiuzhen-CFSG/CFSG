module

public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Representation.Quotient
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Faithful images with central kernel

Passing to the actual linear image changes neither irreducibility nor the
full linear normalizer. If a perfect actor has central kernel, lifting
centralizers identifies its central quotient with the image's central quotient.
In particular a quasisimple actor with central kernel has quasisimple image.

This is the nonfaithful-section reduction needed before applying representation
exclusions to the normalizer in Aschbacher–Smith, *The Classification of
Quasithin Groups*, B.1.11–13, printed pp.72–74. It makes no assertion about
the generalized Fitting subgroup of that normalizer.
-/

public section
namespace Representation.BinaryOffender
open Subgroup Theory.GroupTheory
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Taking the faithful image a second time leaves the subgroup of linear maps unchanged. -/
theorem actionImage_imageRepresentation :
    actionImage (imageRepresentation ρ) = actionImage ρ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Irreducibility descends to the actual faithful image. -/
theorem imageRepresentation_isIrreducible (h : ρ.IsIrreducible) :
    (imageRepresentation ρ).IsIrreducible :=
  (irreducible_comp_surjective_iff (actionHom ρ)
    ρ.asGroupHom.rangeRestrict_surjective (imageRepresentation ρ)).mp h

/-- The normalizers before and after taking the image are the same literal subgroup. -/
theorem linearNormalizer_imageRepresentation :
    linearNormalizer (imageRepresentation ρ) = linearNormalizer ρ := by
  unfold linearNormalizer
  rw [actionImage_imageRepresentation]

/-- In particular the FF condition is unchanged; no identification of an
arbitrary overgroup with the full normalizer is used. -/
theorem isFFModule_normalizer_imageRepresentation_iff :
    IsFFModule (normalizerRepresentation (imageRepresentation ρ)) ↔
      IsFFModule (normalizerRepresentation ρ) := by
  unfold normalizerRepresentation
  rw [linearNormalizer_imageRepresentation]

/-- Perfectness lifts the image center exactly, even when the action has nontrivial kernel. -/
noncomputable def simpleQuotientEquivImage [Group.IsPerfect G]
    (hk : ρ.ker ≤ center G) :
    G ⧸ center G ≃* actionImage ρ ⧸ center (actionImage ρ) := by
  let f := actionHom ρ
  have hf : Function.Surjective f := ρ.asGroupHom.rangeRestrict_surjective
  have hkf : f.ker ≤ center G := by
    intro g hg
    apply hk
    change ρ g = 1
    simpa only [f, imageRepresentation_actionHom, map_one] using
      congrArg (imageRepresentation ρ) (show f g = 1 from hg)
  have hc : (center (actionImage ρ)).comap f = center G := by
    have h := comap_centralizer_map_eq_of_perfect f (⊤ : Subgroup G)
      (by simpa only [coe_top, centralizer_univ] using hkf)
    simpa only [Subgroup.map_top_of_surjective f hf, coe_top, centralizer_univ] using h
  let q := (QuotientGroup.mk' (center (actionImage ρ))).comp f
  have hq : q.ker = center G := by
    rw [show q.ker = (center (actionImage ρ)).comap f by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']]
    exact hc
  exact (QuotientGroup.quotientMulEquivOfEq hq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q
      ((QuotientGroup.mk'_surjective _).comp hf))

/-- Central kernel prevents a quasisimple actor from having trivial image. -/
theorem actionImage_nontrivial_of_central_kernel [IsQuasisimple G]
    (hk : ρ.ker ≤ center G) : Nontrivial (actionImage ρ) := by
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  let : Nontrivial (actionImage ρ ⧸ center (actionImage ρ)) :=
    (simpleQuotientEquivImage ρ hk).symm.surjective.nontrivial
  exact (QuotientGroup.mk'_surjective (center (actionImage ρ))).nontrivial

/-- The section image is quasisimple, with no faithfulness assumption on the original actor. -/
theorem actionImage_quasisimple_of_central_kernel [IsQuasisimple G]
    (hk : ρ.ker ≤ center G) : IsQuasisimple (actionImage ρ) := by
  let := actionImage_nontrivial_of_central_kernel ρ hk
  exact IsQuasisimple.of_surjective (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective

end Representation.BinaryOffender
