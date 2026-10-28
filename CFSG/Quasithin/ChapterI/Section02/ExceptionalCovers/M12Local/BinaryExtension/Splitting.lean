module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.BinaryExtension.CentralizerQuotient
public import Theory.GroupTheory.ElementaryS3CentralRetraction

/-!
# Splitting the elementary branch of the marked M₁₂ centralizer

Apply the elementary-kernel S₃ splitting theorem to the literal full centralizer
modulo the marked square line. The kernel is elementary when the quadratic
form vanishes; the cubic lift, its fixed subgroup, and the extra involution
are those in `CentralizerQuotientData`. Pulling back the quotient retraction
splits off the actual ambient center in `C_K(u)`.

The structural realization `s` remains explicit and is constructed in
`BinaryExtension.Realization`. Final source assembly belongs to
`BinaryExtension`; this module proves the independent splitting implication.

Source: Aschbacher–Smith, I.2.2(5), printed p.412 / PDF p.423.
-/

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
namespace MarkedSquareCoordinates
variable {K : Type*} [Group K] [Finite K] {u : K}
variable {e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12}
variable {m : Sporadic.Mathieu.M12SmallPair.CoverOrbitData}

/-- The vanishing quadratic form gives the source's actual centralizer
retraction, using the realized S₃ quotient and its marked lifts. -/
public theorem centralizerRetraction_of_quadratic_eq_zero
    (d : MarkedSquareCoordinates e u m) (hZ : Nat.card (center K) = 2)
    (s : d.CentralizerQuotientData) (hq : d.quadratic = 0) :
    Nonempty (CentralizerRetraction u) := by
  obtain ⟨r, hr⟩ := exists_central_retraction_of_elementary_s3_quotient
    s.projection s.projection_surjective (s.kernel_elementary hq)
    d.centerEmbedding.range s.center_le_kernel d.centerEmbedding_range_le_center
    (d.centerEmbedding_range_card hZ)
    (QuotientGroup.mk' d.centralizerLine d.cubicInCentralizer)
    (by rw [← map_pow, d.cubicInCentralizer_cube, map_one])
    s.cubic_image_order s.cubic_fixed_iff
    (QuotientGroup.mk' d.centralizerLine s.extra)
    (by rw [← map_pow, s.extra_square, map_one]) s.extra_image_order
  exact d.centralizerRetraction_of_quotient r hr

end MarkedSquareCoordinates
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
