module

public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Representation.Quotient
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.PGroupCore

/-!
# Faithful images of irreducible quasisimple FF actions

An action with central kernel is a perfect central cover of its actual
linear image. The image therefore has the same simple central quotient.
Surjective pullback preserves irreducibility, and the normal p-subgroup
fixed-vector argument removes the two-core of the faithful binary image.
Finally, taking this image a second time changes neither its subgroup of
GL(V) nor the full linear normalizer or its tautological action.

These are the faithful-image reductions used before applying the general
FF classification in Aschbacher–Smith, B.1.13, printed p.73. They do not
identify the original covering group with the image.
-/

public section
open Subgroup Theory.GroupTheory
namespace Representation.BinaryOffender
variable {L V : Type*} [Group L] [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) L V)

/-- The faithful image has exactly the original invariant subspaces. -/
theorem imageRepresentation_irreducible (hi : IsIrreducible σ) :
    IsIrreducible (imageRepresentation σ) :=
  (irreducible_comp_surjective_iff (actionHom σ)
    σ.asGroupHom.rangeRestrict_surjective (imageRepresentation σ)).mp hi

/-- The second image is the same literal subgroup of invertible endomorphisms. -/
@[simp] theorem actionImage_imageRepresentation :
    actionImage (imageRepresentation σ) = actionImage σ := by
  have he (x : actionImage σ) : (imageRepresentation σ).asGroupHom x = x.val :=
    Units.ext rfl
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [he]
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, he ⟨x, hx⟩⟩

/-- Faithful-image passage preserves the full-normalizer FF hypothesis exactly. -/
theorem normalizer_isFF_imageRepresentation_iff :
    IsFFModule (normalizerRepresentation (imageRepresentation σ)) ↔
      IsFFModule (normalizerRepresentation σ) := by
  unfold normalizerRepresentation linearNormalizer
  rw [actionImage_imageRepresentation]

variable [Group.IsPerfect L]

/-- The actual action homomorphism as a perfect central cover. -/
def actionCover (hk : σ.ker ≤ center L) :
    PerfectCentralCovering.Cover L (actionImage σ) where
  toMonoidHom := actionHom σ
  surjective := σ.asGroupHom.rangeRestrict_surjective
  isPerfect := inferInstance
  ker_le_center := by
    intro x hx
    apply hk
    change σ x = 1
    simpa only [imageRepresentation_actionHom, map_one] using
      congrArg (imageRepresentation σ) (show actionHom σ x = 1 from hx)

/-- The central quotient of the faithful image retains the original central quotient. -/
noncomputable def actionImageQuotientCenterEquiv (hk : σ.ker ≤ center L) :
    L ⧸ center L ≃* actionImage σ ⧸ center (actionImage σ) :=
  (actionCover σ hk).quotientCenterEquiv

omit [Group.IsPerfect L] in
/-- A central-kernel image of a quasisimple group is quasisimple. -/
theorem actionImage_isQuasisimple [IsQuasisimple L] (hk : σ.ker ≤ center L) :
    IsQuasisimple (actionImage σ) where
  toIsPerfect := Group.IsPerfect.ofSurjective σ.asGroupHom.rangeRestrict_surjective
  simple := (MulEquiv.isSimpleGroup_congr
    (actionImageQuotientCenterEquiv σ hk)).mp IsQuasisimple.simple

omit [Group.IsPerfect L] in
/-- A faithful irreducible binary image has trivial two-core, regardless of the
kernel of the original action. -/
theorem actionImage_twoCore_eq_bot [Finite L] [FiniteDimensional (ZMod 2) V]
    (hi : IsIrreducible σ) : pCore 2 (actionImage σ) = ⊥ := by
  let := imageRepresentation_irreducible σ hi
  have hk := normal_p_subgroup_le_ker (imageRepresentation σ)
    (pCore 2 (actionImage σ)) (pCore_isPGroup (p := 2))
  exact bot_unique (hk.trans ((MonoidHom.ker_eq_bot_iff _).mpr
    (imageRepresentation_injective σ)).le)

end Representation.BinaryOffender
