module
public import CFSG.Quasithin.ChapterG.Section09.Setup
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.Models

/-!
# Binary self-duality excludes natural SL₃ constituents

Two elementary matrices force the first coordinate line into the radical of
any binary invariant bilinear form on the natural three-dimensional field
module. Thus neither the natural nor inverse-transpose action is binary
self-dual. Explicit transport retains the specified group isomorphism,
module coordinates and covering homomorphism. This avoids identifying the
field-linear dual with the binary dual.

Source: Aschbacher–Smith G.11.7–8, printed pp.366–369, applying the
self-duality of the original marked constituent to the G.9.3(8) row.
-/

@[expose] public noncomputable section
open Matrix Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedLinearThree
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
variable {k : Type*} [Field k] [Algebra (ZMod 2) k]

private def r : SL(3,k) := ⟨!![1,0,1; 0,1,0; 0,0,1], by simp [Matrix.det_fin_three]⟩
private def t : SL(3,k) := ⟨!![1,1,0; 0,1,0; 0,0,1], by simp [Matrix.det_fin_three]⟩
private lemma r_apply (w : Fin 3 → k) :
    naturalBinary k r w = ![w 0 + w 2, w 1, w 2] := by
  change (r (k := k)).val.mulVec w = _
  funext i
  fin_cases i <;> simp [r, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
private lemma t_apply (w : Fin 3 → k) :
    naturalBinary k t w = ![w 0 + w 1, w 1, w 2] := by
  change (t (k := k)).val.mulVec w = _
  funext i
  fin_cases i <;> simp [t, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The binary natural SL₃ action is not self-dual over any coefficient field. -/
theorem natural_not_selfDual :
    ¬ Nonempty ((naturalBinary k).Equiv (naturalBinary k).dual) := by
  rintro ⟨e⟩
  let B : LinearMap.BilinForm (ZMod 2) (Fin 3 → k) := e.toLinearEquiv.toLinearMap
  have hpres (g : SL(3,k)) (u w : Fin 3 → k) :
      B (naturalBinary k g u) (naturalBinary k g w) = B u w := by
    have hh := LinearMap.congr_fun (e.isIntertwining' g) u
    have hh' := LinearMap.congr_fun hh (naturalBinary k g w)
    change B (naturalBinary k g u) (naturalBinary k g w) =
      B u (naturalBinary k g⁻¹ (naturalBinary k g w)) at hh'
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using hh'
  have hzero (a b : k) : B ![a,0,0] ![b,0,0] = 0 := by
    have h := hpres r ![0,0,a] ![b,0,0]
    rw [r_apply, r_apply] at h
    have he : (![a,0,a] : Fin 3 → k) = ![0,0,a] + ![a,0,0] := by
      funext i; fin_cases i <;> simp
    change B ![0+a,0,a] ![b+0,0,0] = B ![0,0,a] ![b,0,0] at h
    rw [zero_add, add_zero] at h
    rw [he, map_add, LinearMap.add_apply] at h
    exact add_eq_left.mp h
  have hfirst (a b : k) : B ![a,0,0] ![0,b,0] = 0 := by
    have h := hpres r ![0,0,a] ![0,b,0]
    rw [r_apply, r_apply] at h
    have he : (![a,0,a] : Fin 3 → k) = ![0,0,a] + ![a,0,0] := by
      funext i; fin_cases i <;> simp
    change B ![0+a,0,a] ![0+0,b,0] = B ![0,0,a] ![0,b,0] at h
    simp only [zero_add] at h
    rw [he, map_add, LinearMap.add_apply] at h
    exact add_eq_left.mp h
  have hsecond (a b : k) : B ![a,0,0] ![0,0,b] = 0 := by
    have h := hpres t ![0,a,0] ![0,0,b]
    rw [t_apply, t_apply] at h
    have he : (![a,a,0] : Fin 3 → k) = ![0,a,0] + ![a,0,0] := by
      funext i; fin_cases i <;> simp
    change B ![0+a,a,0] ![0+0,0,b] = B ![0,a,0] ![0,0,b] at h
    simp only [zero_add] at h
    rw [he, map_add, LinearMap.add_apply] at h
    exact add_eq_left.mp h
  have hkill : e ![1,0,0] = 0 := by
    apply LinearMap.ext
    intro w
    change B ![1,0,0] w = 0
    have hw : w = ![w 0,0,0] + ![0,w 1,0] + ![0,0,w 2] := by
      funext i; fin_cases i <;> simp
    rw [hw, map_add, map_add, hzero, hfirst, hsecond, add_zero, add_zero]
  have h := e.injective (hkill.trans e.map_zero.symm)
  exact one_ne_zero (congrArg (fun w : Fin 3 → k => w 0) h)
section Transport
variable {D J V W : Type*} [Group D] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- Self-duality transports through the specified group and module isomorphisms. -/
theorem selfDual_of_quasiequivalent
    (ρ : Representation (ZMod 2) D V) (σ : Representation (ZMod 2) J W)
    (hm : ChapterG.Section09.Quasiequivalent ρ σ)
    (hs : Nonempty (ρ.Equiv ρ.dual)) : Nonempty (σ.Equiv σ.dual) := by
  obtain ⟨a,c,hc⟩ := hm
  obtain ⟨e⟩ := hs
  have hi (g : J) (w : W) : c.symm (σ g w) = ρ (a.symm g) (c.symm w) := by
    apply c.injective
    rw [c.apply_symm_apply, hc, a.apply_symm_apply, c.apply_symm_apply]
  refine ⟨.mk (c.symm.trans (e.toLinearEquiv.trans c.symm.dualMap)) ?_⟩
  intro g
  apply LinearMap.ext
  intro w
  apply LinearMap.ext
  intro z
  change e (c.symm (σ g w)) (c.symm z) = e (c.symm w) (c.symm (σ g⁻¹ z))
  rw [hi,hi]
  have he := LinearMap.congr_fun (LinearMap.congr_fun (e.isIntertwining' (a.symm g)) (c.symm w)) (c.symm z)
  change e (ρ (a.symm g) (c.symm w)) (c.symm z) =
    e (c.symm w) (ρ (a.symm g)⁻¹ (c.symm z)) at he
  simpa only [map_inv] using he

/-- Inflation preserves self-duality on the literal covering group. -/
theorem selfDual_comp (ρ : Representation (ZMod 2) D V) (π : J →* D)
    (hs : Nonempty (ρ.Equiv ρ.dual)) :
    Nonempty (Representation.Equiv (ρ.comp π) (Representation.dual (ρ.comp π))) := by
  obtain ⟨e⟩ := hs
  refine ⟨.mk e.toLinearEquiv ?_⟩
  intro g
  apply LinearMap.ext
  intro w
  apply LinearMap.ext
  intro z
  have he := LinearMap.congr_fun (LinearMap.congr_fun (e.isIntertwining' (π g)) w) z
  change e (ρ (π g) w) z = e w (ρ (π g)⁻¹ z) at he
  change e (ρ (π g) w) z = e w (ρ (π g⁻¹) z)
  simpa only [map_inv] using he
end Transport

/-- The inverse-transpose coordinate model is not binary self-dual either. -/
theorem dualNatural_not_selfDual :
    ¬ Nonempty ((dualBinary k).Equiv (dualBinary k).dual) := by
  rintro ⟨e⟩
  apply natural_not_selfDual (k := k)
  refine ⟨.mk e.toLinearEquiv ?_⟩
  intro g
  let h : SL(3,k) := g.transpose⁻¹
  have hh : SpecialLinearGroup.inverseTranspose h = g := by
    change (g.transpose⁻¹)⁻¹.transpose = g
    simp only [inv_inv]
    exact Subtype.ext (Matrix.transpose_transpose _)
  apply LinearMap.ext
  intro w
  apply LinearMap.ext
  intro z
  have he := LinearMap.congr_fun (LinearMap.congr_fun (e.isIntertwining' h) w) z
  change e (naturalBinary k (SpecialLinearGroup.inverseTranspose h) w) z =
    e w (naturalBinary k (SpecialLinearGroup.inverseTranspose h⁻¹) z) at he
  change e (naturalBinary k g w) z = e w (naturalBinary k g⁻¹ z)
  simpa only [map_inv, hh] using he


end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedLinearThree
