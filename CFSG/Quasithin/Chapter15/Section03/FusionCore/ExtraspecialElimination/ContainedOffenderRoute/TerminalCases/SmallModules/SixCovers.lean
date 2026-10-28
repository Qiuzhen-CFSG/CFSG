module

public import Theory.Representation.BinaryPermutationSixCover
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceActions.Geometry

/-!
# Recovering the six-letter moved module from its central quotient

A perfect central cover of the natural A₆-module is the natural module or
the augmentation core. The recognition retains the original marking of the
whole actor, whether A₆ or S₆. For a moved section the covering map is the
literal quotient map followed by supplied quotient coordinates. Its kernel
is central by construction; the Irr⁺ condition supplies perfectness.

These results discharge central-cover recovery in the A₆ paragraph of
15.3.49. Quotient-coordinate selection from B.5.1 and terminal point exclusion
remain with their assembly owners; no classification premise is inferred
from an abstract group-family label.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.2–3,
printed pp.83–84, and 15.3.49, printed p.1145.
-/

@[expose] public section
open Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.SmallModules.SixCovers
open ModelExclusions BinaryPermutation

variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- The alternating perfect-central-cover recognition, packaged for the
terminal point argument with the same actor equivalence. -/
theorem alternating_case (σ : Representation (ZMod 2) D W)
    (J : Subgroup D) (e : D ≃* alternatingGroup (Fin 6)) (hJ : J = ⊤)
    (f : W →ₗ[ZMod 2] natural (Fin 6))
    (hf : ∀ g w, f (σ g w) = naturalRepresentation (Fin 6) (e g).val (f w))
    (hsur : Function.Surjective f)
    (hker : f.ker ≤ fixedSpace σ J)
    (hgen : subspaceCommutator σ ⊤ J = ⊤) : PointCases.SixModuleCase σ J := by
  rcases SixCover.naturalOrCore_alternating σ e J hJ f hf hsur hker hgen with
    ⟨E, hE⟩ | ⟨E, hE⟩
  · exact .naturalAlternating e hJ E hE
  · exact .coreAlternating e hJ E hE

/-- The symmetric perfect-central-cover recognition, retaining the marked
alternating component inside the whole actor. -/
theorem symmetric_case (σ : Representation (ZMod 2) D W)
    (J : Subgroup D) (e : D ≃* Equiv.Perm (Fin 6))
    (hJ : J.map e.toMonoidHom = alternatingGroup (Fin 6))
    (f : W →ₗ[ZMod 2] natural (Fin 6))
    (hf : ∀ g w, f (σ g w) = naturalRepresentation (Fin 6) (e g) (f w))
    (hsur : Function.Surjective f)
    (hker : f.ker ≤ fixedSpace σ J)
    (hgen : subspaceCommutator σ ⊤ J = ⊤) : PointCases.SixModuleCase σ J := by
  rcases SixCover.naturalOrCore_symmetric σ e J hJ f hf hsur hker hgen with
    ⟨E, hE⟩ | ⟨E, hE⟩
  · exact .naturalSymmetric e hJ E hE
  · exact .coreSymmetric e hJ E hE

omit [FiniteDimensional (ZMod 2) W] in
private theorem moved_generated (ρ : Representation (ZMod 2) D W)
    (J : Subgroup D) (c : MovedSection ρ J)
    (hi : IsIrrPlus ρ J c.space.toSubmodule) :
    subspaceCommutator c.space.toRepresentation ⊤ J = ⊤ := by
  apply Submodule.map_injective_of_injective c.space.toSubmodule.subtype_injective
  have hh := subspaceCommutator_map_embedding ρ c.space.toRepresentation (MonoidHom.id D)
    c.space.toSubmodule.subtype (fun _ _ => rfl) J ⊤
  simpa only [Subgroup.map_id, Submodule.map_top, Submodule.range_subtype, hi.choose_spec.1]
    using hh.symm

omit [FiniteDimensional (ZMod 2) W] in
private theorem coordinates_kernel (ρ : Representation (ZMod 2) D W)
    (J : Subgroup D) (c : MovedSection ρ J)
    (E : (c.space.toSubmodule ⧸ c.central.toSubmodule) ≃ₗ[ZMod 2] natural (Fin 6)) :
    (E.toLinearMap.comp c.central.toSubmodule.mkQ).ker ≤
      fixedSpace c.space.toRepresentation J := by
  intro w hw
  have hq : c.central.toSubmodule.mkQ w = 0 :=
    E.injective (show E (c.central.toSubmodule.mkQ w) = E 0 by simpa using hw)
  rw [← c.central_eq]
  exact (Submodule.Quotient.mk_eq_zero _).mp hq

/-- Recover the alternating moved-space case from coordinates on its literal
fixed-space quotient. Irr⁺ discharges the covering perfectness hypothesis. -/
theorem moved_alternating (ρ : Representation (ZMod 2) D W)
    (J : Subgroup D) (c : MovedSection ρ J)
    (hi : IsIrrPlus ρ J c.space.toSubmodule)
    (a : ActionEquiv c.action (alternatingNaturalRepresentation (Fin 6)))
    (hJ : J = ⊤) : PointCases.SixModuleCase c.space.toRepresentation J := by
  let f : c.space.toSubmodule →ₗ[ZMod 2] natural (Fin 6) :=
    a.linearEquiv.toLinearMap.comp c.central.toSubmodule.mkQ
  apply alternating_case c.space.toRepresentation J a.groupEquiv hJ f
  · intro g w
    exact a.intertwines g (c.central.toSubmodule.mkQ w)
  · exact a.linearEquiv.surjective.comp c.central.toSubmodule.mkQ_surjective
  · exact coordinates_kernel ρ J c a.linearEquiv
  · exact moved_generated ρ J c hi

/-- Recover the symmetric moved-space case from quotient coordinates whose
marking sends the actual component to A₆. The projection and both actions
remain those of the given moved section. -/
theorem moved_symmetric (ρ : Representation (ZMod 2) D W)
    (J : Subgroup D) (c : MovedSection ρ J)
    (hi : IsIrrPlus ρ J c.space.toSubmodule)
    (a : ActionEquiv c.action (naturalRepresentation (Fin 6)))
    (hJ : J.map a.groupEquiv.toMonoidHom = alternatingGroup (Fin 6)) :
    PointCases.SixModuleCase c.space.toRepresentation J := by
  let f : c.space.toSubmodule →ₗ[ZMod 2] natural (Fin 6) :=
    a.linearEquiv.toLinearMap.comp c.central.toSubmodule.mkQ
  apply symmetric_case c.space.toRepresentation J a.groupEquiv hJ f
  · intro g w
    exact a.intertwines g (c.central.toSubmodule.mkQ w)
  · exact a.linearEquiv.surjective.comp c.central.toSubmodule.mkQ_surjective
  · exact coordinates_kernel ρ J c a.linearEquiv
  · exact moved_generated ρ J c hi

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.SmallModules.SixCovers
