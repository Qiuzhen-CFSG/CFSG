module

public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeBinary
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.ModelOffenders.ExplicitOffenders.InvolutionDisplacement.InvolutionClass

/-!
# Involution-fixed vectors in the binary natural extension

A natural cocycle that vanishes at a nonidentity involution is principal.
Conjugacy reduces the involution to an elementary transvection, where the
spare coordinate of the exceptional cocycle detects its coefficient. This
retains the nonsplit extension: that coefficient is forced to vanish by the
fixed-vector hypothesis, rather than by an assumed splitting.

Consequently, in any extension of a marked binary natural submodule by a
trivial module, an involution-fixed vector belongs to the natural submodule
plus the whole-group fixed space. No finiteness of the extension is needed.
This is the module calculation for the dual application of MS93 (1.5)(i).
Its application to the actual amalgam quotient remains a separate step.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (1.5)(i), printed p.843, used in (4.2)(i), printed p.882. The checked
binary cocycle normal form comes from the project's formalization of
Aschbacher--Smith I.1.6(4).
-/

public section

open Matrix Matrix.SpecialLinearGroup Representation Representation.OneCohomology
open Representation.OneCohomology.SLHigherNatural
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Transfer.SpanBound
private abbrev SL := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
private abbrev rho := specialLinearNatural (k := ZMod 2) 3
private abbrev t : SL := transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : ZMod 2)

private theorem principal_of_transvection_value (f : cocycles rho) (v : Fin 3 → ZMod 2)
    (hf : f.val t = rho t v - v) : ∃ u, principal rho u = f := by
  obtain ⟨a, u, hu⟩ := SLThreeBinary.normal_form f
  have hs := congrArg (fun x : Fin 3 → ZMod 2 => x 2) hf
  rw [hu] at hs
  change a * SLThreeBinary.exceptional.val t 2 + (principal rho u).val t 2 =
    (rho t v - v) 2 at hs
  rw [SLThreeBinary.exceptional_spare 0 1 2 (by decide) (by decide) (by decide)] at hs
  have hp (w : Fin 3 → ZMod 2) : (rho t w - w) 2 = 0 := by
    simp [rho, t, action_transvection]
  change a * 1 + (rho t u - u) 2 = (rho t v - v) 2 at hs
  rw [hp u, hp v, mul_one, add_zero] at hs
  exact ⟨u, by simpa [hs] using hu.symm⟩

/-- Vanishing at one nonidentity involution detects principal binary natural cocycles. -/
theorem cocycle_principal_of_involution_zero (f : cocycles (specialLinearNatural (k := ZMod 2) 3))
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hg : g ^ 2 = 1) (hne : g ≠ 1) (hf : f.val g = 0) :
    ∃ u : Fin 3 → ZMod 2, principal (specialLinearNatural (k := ZMod 2) 3) u = f := by
  obtain ⟨c, hc⟩ :=
    AbelianCore.DoubleCopy.CoverModels.ModelOffenders.InvolutionDisplacement.involution_conjugate_transvection
      g hg hne
  let v := rho c⁻¹ (f.val c)
  have hcv : rho c v = f.val c := by
    simp only [v, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  have h := congrArg f.val hc
  rw [f.property, f.property, hf, add_zero] at h
  have ht : f.val t = rho t v - v := by
    apply (show Function.Injective (rho c) from fun x y hxy => by
      have hh := congrArg (rho c⁻¹) hxy
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply] using hh)
    rw [map_sub, hcv, ← Module.End.mul_apply, ← map_mul, ← hc,
      map_mul, Module.End.mul_apply, hcv]
    exact eq_sub_iff_add_eq.mpr h.symm
  exact principal_of_transvection_value f v ht

/-- A vector fixed by an involution in an extension of a marked natural
submodule by a trivial module lies in the natural submodule plus the fixed space.
The exceptional nonsplit extension is retained in the cocycle normal form. -/
theorem fixed_involution_mem_natural_sup_fixed
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) W) (N : Subrepresentation σ)
    (marking : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (e : N.toSubmodule ≃ₗ[ZMod 2] (Fin 3 → ZMod 2))
    (he : ∀ g v, e (N.toRepresentation g v) = specialLinearNatural (k := ZMod 2) 3 (marking g) (e v))
    (htriv : HasTrivialQuotient N)
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (hg : g ^ 2 = 1) (hne : g ≠ 1)
    (w : W) (hw : σ g w = w) : w ∈ N.toSubmodule ⊔ fixed σ := by
  let T := cocyclesCongr N.toRepresentation rho marking e he
  let f := displacementCocycle N htriv w
  have hf : (T f).val (marking g) = 0 := by
    change e (f.val (marking.symm (marking g))) = 0
    rw [marking.symm_apply_apply]
    change e (⟨σ g w - w, htriv g w⟩ : N.toSubmodule) = 0
    rw [show (⟨σ g w - w, htriv g w⟩ : N.toSubmodule) = 0 by
      apply Subtype.ext
      exact sub_eq_zero.mpr hw, map_zero]
  obtain ⟨u, hu⟩ := cocycle_principal_of_involution_zero (T f) (marking g)
    (by rw [← map_pow, hg, map_one]) (by simpa using hne) hf
  apply (extensionClass_eq_zero_iff N htriv w).mp
  apply (classMap_eq_zero_iff N.toRepresentation f).mpr
  refine ⟨e.symm u, T.injective ?_⟩
  simpa only [T, cocyclesCongr_principal, e.apply_symm_apply] using hu
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Transfer.SpanBound
