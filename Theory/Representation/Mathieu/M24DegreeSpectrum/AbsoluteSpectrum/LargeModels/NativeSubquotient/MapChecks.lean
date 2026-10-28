module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Packed
/-!
# Separate sparse mask and product certificates

Reconstructing the masks separately from checking the row products avoids
repeated reduction in a recursive conjunction. The three list equalities
imply the existing rectangular matrix checker. The native 1242 and 1792
certificates use this lemma in bounded sequential batches.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Packed
open Degree220Pair.NativeActions.CertificatePacked
open Degree320Pair.MatrixCertificates.TraceRows

theorem checkEqualProducts_of_gap_maps (ys ws xs zs : List ℕ) (as bs : List (List ℕ))
    (hx : as.map gapMask = xs) (hz : bs.map gapMask = zs)
    (hp : as.map (gapRow ys) = bs.map (gapRow ws)) :
    checkEqualProducts ys ws xs zs = true := by
  subst xs zs
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [checkEqualProducts]
  | cons a as ih =>
    cases bs with
    | nil => simp at hp
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at hp
      simp only [List.map_cons, checkEqualProducts, Bool.and_eq_true, beq_iff_eq]
      exact ⟨by simpa only [gapRow_combine] using hp.1, ih bs hp.2⟩
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Packed
