module
public import CFSG.Quasithin.ChapterG.Section09.ConstituentActionDual
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Reversing the component comparison in G.9

Ordinary quasiequivalence is symmetric. A dual quasiequivalence reverses
using the canonical evaluation map to the double dual. This lets the
exchanged constituent argument select either of its actual components.
-/
@[expose] public noncomputable section
open Subgroup Module Representation
namespace CFSG.Quasithin.ChapterG.Section09
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)

theorem quasiequivalent_symm (h : Quasiequivalent ρ σ) : Quasiequivalent σ ρ := by
  obtain ⟨e,t,ht⟩ := h
  refine ⟨e.symm,t.symm,?_⟩
  intro d w
  apply t.injective
  simp only [LinearEquiv.apply_symm_apply]
  simpa only [MulEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] using
    (ht (e.symm d) (t.symm w)).symm

theorem quasiequivalent_dual_symm [FiniteDimensional (ZMod 2) W]
    (h : Quasiequivalent ρ (Representation.dual σ)) :
    Quasiequivalent σ (Representation.dual ρ) := by
  obtain ⟨e,t,ht⟩ := h
  refine ⟨e.symm,(Module.evalEquiv (ZMod 2) W).trans t.dualMap,?_⟩
  intro d w
  ext v
  change t v (σ d w) = t (ρ (e.symm d)⁻¹ v) w
  have hh := congrArg (fun l => l w) (ht (e.symm d)⁻¹ v)
  simp only [map_inv,MulEquiv.apply_symm_apply,Representation.dual_apply,inv_inv] at hh
  exact hh.symm
end CFSG.Quasithin.ChapterG.Section09
