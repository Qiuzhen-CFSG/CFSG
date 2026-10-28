module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Representatives

/-!
# Distinct marked HS involution classes

The short word `t` squares to one and fixes none of the 100 letters. The
central representative `e0` fixes zero. Conjugation preserves existence of a
fixed letter, so these representatives belong to different carrier classes.

Source: ATLAS HSG1-p100B0; the two inner classes in GLS3 Table 5.3m.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
set_option maxRecDepth 100000

/-- The product-class representative has no fixed letter in the defining action. -/
theorem t_fixedPointFree : ∀ p : Fin 100, inclusion t p ≠ p := by
  apply Certificate.allFin
  decide +kernel

/-- The marked product-class representative really is an involution. -/
theorem t_order : orderOf t = 2 := by
  apply orderOf_eq_prime_iff.mpr
  constructor
  · apply inclusion_injective
    apply Equiv.ext
    apply Certificate.allFin
    decide +kernel
  · intro h
    exact t_fixedPointFree 0 (by rw [h, map_one]; rfl)

/-- The two marked representatives are not conjugate even as degree-100 permutations. -/
theorem representatives_not_isConj : ¬ IsConj e0 t := by
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have he : g * e0 * g⁻¹ = t := hg
  have ht : t * g = g * e0 := ((mul_inv_eq_iff_eq_mul).mp he).symm
  have h0 : inclusion e0 0 = 0 := by decide +kernel
  have hp := congrArg (fun x : Carrier => inclusion x 0) ht
  apply t_fixedPointFree (inclusion g 0)
  simpa only [map_mul, Equiv.Perm.mul_apply, h0] using hp

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage
