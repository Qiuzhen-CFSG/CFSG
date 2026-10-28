module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.Coordinates
public import Mathlib.Tactic.Abel

/-!
# Actual extension cochains satisfy the adjacent-generator relations

An actual upper-right cochain of a representation extension satisfies the
multiplication rule. Applying it to the square, commuting-pair and braid
identities of the seven adjacent transpositions gives the matrix relations
used by the finite linear certificates. The argument works for both natural
self-extensions and augmentation-core-by-natural extensions, with their
specified constituent actions retained throughout.

Source: Aschbacher–Smith, Lemma 14.7.51, printed p.1065, refs/quasithin.pdf.
-/

public section
open Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension

section Generic
variable {k G U W : Type*} [Field k] [Group G]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  (τ : Representation k G U) (σ : Representation k G W)
  (d : G → W →ₗ[k] U)
  (hd : ∀ g h, d (g*h) = (τ g).comp (d h) + (d g).comp (σ h))

include hd

private theorem cochain_one : d 1 = 0 := by
  have h := hd 1 1
  simp only [one_mul,map_one,Module.End.one_eq_id,LinearMap.id_comp,LinearMap.comp_id] at h
  exact add_eq_left.mp h.symm

private theorem cochain_square (g : G) (hg : g*g=1) :
    (τ g).comp (d g) + (d g).comp (σ g) = 0 := by
  rw [← hd,hg,cochain_one τ σ d hd]

private theorem cochain_commute (g h : G) (hgh : g*h=h*g) :
    (τ g).comp (d h) + (d g).comp (σ h) =
      (τ h).comp (d g) + (d h).comp (σ g) := by
  rw [←hd,←hd,hgh]

private theorem cochain_triple (g h a : G) :
    d (g*h*a) = ((τ g).comp (τ h)).comp (d a) +
      ((τ g).comp (d h)).comp (σ a) + ((d g).comp (σ h)).comp (σ a) := by
  rw [hd (g*h) a,hd g h,map_mul,Module.End.mul_eq_comp,
    LinearMap.add_comp]
  abel

private theorem cochain_braid (g h : G) (hgh : g*h*g=h*g*h) :
    ((τ g).comp (τ h)).comp (d g) +
        ((τ g).comp (d h)).comp (σ g) + ((d g).comp (σ h)).comp (σ g) =
      ((τ h).comp (τ g)).comp (d h) +
        ((τ h).comp (d g)).comp (σ h) + ((d h).comp (σ g)).comp (σ h) := by
  rw [←cochain_triple τ σ d hd,←cochain_triple τ σ d hd,hgh]
end Generic

/-- An actual natural self-extension cochain obeys the seven matrix relations. -/
theorem relations_of_cocycle
    (τ σ : Representation (ZMod 2) (Equiv.Perm (Fin 8)) V)
    (d : Equiv.Perm (Fin 8) → V →ₗ[ZMod 2] V)
    (hd : ∀ g h, d (g*h) = (τ g).comp (d h) + (d g).comp (σ h))
    (hτ : ∀ i, τ (adjacent i) = (A i).mulVecLin)
    (hσ : ∀ i, σ (adjacent i) = (A i).mulVecLin) :
    Relations (fun i => LinearMap.toMatrix' (d (adjacent i))) := by
  have hτm (i) : LinearMap.toMatrix' (τ (adjacent i)) = A i := by
    rw [hτ]
    exact LinearMap.toMatrix'_toLin' _
  have hσm (i) : LinearMap.toMatrix' (σ (adjacent i)) = A i := by
    rw [hσ]
    exact LinearMap.toMatrix'_toLin' _
  constructor
  · intro i
    have h := congrArg LinearMap.toMatrix'
      (cochain_square τ σ d hd (adjacent i) (adjacent_square i))
    simpa only [map_add,map_zero,LinearMap.toMatrix'_comp,hτm,hσm] using h
  · intro i j hij
    have h := congrArg LinearMap.toMatrix'
      (cochain_commute τ σ d hd (adjacent i) (adjacent j) (adjacent_commute i j hij))
    simpa only [map_add,LinearMap.toMatrix'_comp,hτm,hσm] using h
  · intro i j hij
    have h := congrArg LinearMap.toMatrix'
      (cochain_braid τ σ d hd (adjacent i) (adjacent j) (adjacent_braid i j hij))
    simpa only [map_add,LinearMap.toMatrix'_comp,hτm,hσm] using h

/-- Core-by-natural cochains give the same relations with rectangular upper blocks. -/
theorem coreRelations_of_cocycle
    (τ : Representation (ZMod 2) (Equiv.Perm (Fin 8)) CoreV)
    (σ : Representation (ZMod 2) (Equiv.Perm (Fin 8)) V)
    (d : Equiv.Perm (Fin 8) → V →ₗ[ZMod 2] CoreV)
    (hd : ∀ g h, d (g*h) = (τ g).comp (d h) + (d g).comp (σ h))
    (hτ : ∀ i, τ (adjacent i) = (CoreA i).mulVecLin)
    (hσ : ∀ i, σ (adjacent i) = (A i).mulVecLin) :
    CoreRelations (fun i => LinearMap.toMatrix' (d (adjacent i))) := by
  have hτm (i) : LinearMap.toMatrix' (τ (adjacent i)) = CoreA i := by
    rw [hτ]
    exact LinearMap.toMatrix'_toLin' _
  have hσm (i) : LinearMap.toMatrix' (σ (adjacent i)) = A i := by
    rw [hσ]
    exact LinearMap.toMatrix'_toLin' _
  constructor
  · intro i
    have h := congrArg LinearMap.toMatrix'
      (cochain_square τ σ d hd (adjacent i) (adjacent_square i))
    simpa only [map_add,map_zero,LinearMap.toMatrix'_comp,hτm,hσm] using h
  · intro i j hij
    have h := congrArg LinearMap.toMatrix'
      (cochain_commute τ σ d hd (adjacent i) (adjacent j) (adjacent_commute i j hij))
    simpa only [map_add,LinearMap.toMatrix'_comp,hτm,hσm] using h
  · intro i j hij
    have h := congrArg LinearMap.toMatrix'
      (cochain_braid τ σ d hd (adjacent i) (adjacent j) (adjacent_braid i j hij))
    simpa only [map_add,LinearMap.toMatrix'_comp,hτm,hσm] using h
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
