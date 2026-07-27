import Submission.ZStar.HigmanScratch
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.LocalRing.Basic

/-!
The Jacobson correction used in the order-two relative-trace argument.

The point is deliberately stated at the corner level.  If an idempotent
corner has identity equal to a relative-trace term modulo a nonunit, then the
error can be absorbed into the inverse of `1 - error` in the corner.  The
remaining representation-specific work is only to provide the right-
linearity of the relative trace by corner units.
-/

noncomputable section

namespace Submission.ZStar
namespace CornerTraceCorrection

universe u v

open IsIdempotentElem

theorem exists_exact_corner_trace_of_jacobson_error
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (f : A) (hf : IsIdempotentElem f)
    [IsLocalRing hf.Corner]
    (T : A →+ hf.Corner)
    (c : A) (r : hf.Corner)
    (hdecomp : (1 : hf.Corner) = T c + r)
    (hr : r ∈ nonunits hf.Corner)
    (hTmul : ∀ (a : A) (u : hf.Corner),
      T (a * u.1) = T a * u) :
    ∃ c' : A, T c' = 1 := by
  have hu : IsUnit ((1 : hf.Corner) - r) := by
    have hor : IsUnit r ∨ IsUnit ((1 : hf.Corner) - r) :=
      IsLocalRing.isUnit_or_isUnit_of_add_one (by
        abel)
    exact hor.resolve_left hr
  let U : (hf.Corner)ˣ := hu.unit
  have hU : (U : hf.Corner) = (1 : hf.Corner) - r := hu.unit_spec
  let u : hf.Corner := ↑U⁻¹
  have huinv : ((1 : hf.Corner) - r) * u = 1 := by
    rw [← hU]
    exact Units.mul_inv U
  have hTc : T c = (1 : hf.Corner) - r := by
    have h : (1 : hf.Corner) - r = T c :=
      sub_eq_iff_eq_add.mpr hdecomp
    exact h.symm
  refine ⟨c * u.1, ?_⟩
  rw [hTmul, hTc]
  exact huinv

end CornerTraceCorrection
end Submission.ZStar
