module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The binary natural and contragredient actions in MS93

A covector stabilizer in SL₃(2) fixes no nonzero natural vector. Consequently
any equivariant function from the dual three-space to the natural three-space
is zero; linearity is not needed. This applies to the literal square map of a
central extension. Transitivity on nonzero covectors is also recorded for the
radical argument with two dual factors.

The two finite certificates enumerate the actual determinant-one matrices and
are checked by kernel reduction. The transpose version avoids evaluating matrix
inverses during enumeration; the subsequent theorems use inverse transpose.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.11), printed p.909, and the
binary specialization of (4.6.12). These are model calculations, not the
construction of the source's quotient modules.
-/

@[expose] public section

open Matrix
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Linear
abbrev W := Fin 3 → ZMod 2
abbrev S := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem stabilizer_certificate : ∀ v w : W, w ≠ 0 →
    ∃ g : S, g.val.transpose.mulVec v = v ∧ g.val.mulVec w ≠ w := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem orbit_certificate : ∀ v w : W, v ≠ 0 → w ≠ 0 →
    ∃ g : S, g.val.transpose.mulVec v = w := by
  decide +kernel

def dual (g : S) (v : W) : W := (g⁻¹).val.transpose.mulVec v

private theorem natural_inv (g : S) (v : W) : g.val.mulVec ((g⁻¹).val.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
  exact Matrix.one_mulVec v

theorem equivariantDualMap_zero (f : W → W)
    (hf : ∀ (g : S) (v : W), f (dual g v) = g.val.mulVec (f v)) :
    ∀ v, f v = 0 := by
  intro v
  by_contra hn
  obtain ⟨g, hfix, hmove⟩ := stabilizer_certificate v (f v) hn
  have he := hf g⁻¹ v
  have hi : dual g⁻¹ v = v := by simpa only [dual, inv_inv] using hfix
  rw [hi] at he
  apply hmove
  calc
    g.val.mulVec (f v) = g.val.mulVec ((g⁻¹).val.mulVec (f v)) := congrArg _ he
    _ = f v := natural_inv g _

/-- Transitivity of the actual contragredient action away from zero. -/
theorem dual_orbit {v w : W} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : S, dual g v = w := by
  obtain ⟨g, hg⟩ := orbit_certificate v w hv hw
  exact ⟨g⁻¹, by simpa only [dual, inv_inv] using hg⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Linear
