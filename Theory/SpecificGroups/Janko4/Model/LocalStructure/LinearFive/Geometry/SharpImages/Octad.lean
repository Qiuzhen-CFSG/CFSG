module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.SharpImages.Data
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Native
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder
public import Theory.Representation.MathieuCodeRestriction.M22.HexadGeometry

/-!
# The exceptional native octad

The retained vertices of the strict product-bound certificate fix the actual
Golay octad with message 65. The pointwise equations are checked in the same
star coordinates as the native Mathieu quotient, with its specified relabeling.
This identifies the certificate's exception geometrically, for the occurrence
argument of Kleidman--Wilson (1988), Lemma 1.1.2(ii).
-/
@[expose] public section
namespace Janko4.LocalStructure.LinearFive.Geometry.SharpImages
open ElementaryNormalizerCover.ElementaryBound
open Cardinality.QuotientCount.Image
open Sporadic.Mathieu M24LocalGeometry MathieuCode
open SylowCore.FiniteBoundCertificate

def exceptionalOctad : Octad :=
  ⟨m24GolayWord 65, m24GolayWord_mem_blocks_of_card_eq_eight 65 (by decide +kernel)⟩

private theorem keep_fixes : ∀ (v : Fin 192) (p : Fin 24),
    keep v = true → p ∈ exceptionalOctad.val →
      point v (StarOrderCertificate.relabel.symm p) = StarOrderCertificate.relabel.symm p := by
  decide +kernel

/-- Every retained vertex fixes this actual Golay octad pointwise. -/
theorem native_mem_octad_kernel (v : Fin 192) (hv : keep v = true) :
    starGroupEquivM24 (native v).val ∈ octadPointwiseKernel exceptionalOctad := by
  apply (mem_octadPointwiseKernel _ _).mpr
  intro p hp
  change (starGroupEquivM24 (native v).val : Equiv.Perm (Fin 24)) p = p
  rw [starGroupEquivM24_apply]
  change StarOrderCertificate.relabel (perm (vertexIndex v) (StarOrderCertificate.relabel.symm p)) = p
  rw [← point_spec, keep_fixes v p hv hp]
  exact StarOrderCertificate.relabel.apply_symm_apply p

end Janko4.LocalStructure.LinearFive.Geometry.SharpImages
