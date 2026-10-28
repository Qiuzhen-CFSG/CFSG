module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.SmallImages.Data
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.SharpImages.Native

/-!
# The actual fixed octads of the native Mathieu certificate

Each bitset retained by the branching check fixes one explicitly encoded
Golay octad pointwise. The equations use the original star-to-Mathieu
relabeling, so the conclusion concerns the literal quotient marking.
Source: An--O'Brien--Wilson (2003), §4 and Table 1, pp.122,124.
-/
@[expose] public section
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows.SmallImages
open ElementaryNormalizerCover.ElementaryBound
open Cardinality.QuotientCount.Image
open Sporadic.Mathieu M24LocalGeometry MathieuCode
open SylowCore.FiniteBoundCertificate

def octadMessage : Fin 39 → Fin 4096 := ![42, 34, 115, 2230, 2606, 3366, 674, 1450, 50, 99, 1842, 107, 58, 2245, 2564, 3332, 1408, 640, 65, 16, 1857, 24, 73, 2180, 3972, 2188, 3397, 2629, 2580, 3356, 705, 664, 1473, 1424, 1792, 8, 89, 1800, 81]

theorem octad_card : ∀ i, (m24GolayWord (octadMessage i)).card = 8 := by
  decide +kernel

def octad (i : Fin 39) : Octad :=
  ⟨m24GolayWord (octadMessage i), m24GolayWord_mem_blocks_of_card_eq_eight _ (octad_card i)⟩

private theorem keep_fixes : ∀ (i : Fin 39) (v : Fin 192),
    keep i v = true → ∀ p : Fin 24, p ∈ (octad i).val →
      point v (StarOrderCertificate.relabel.symm p) = StarOrderCertificate.relabel.symm p := by
  decide +kernel

/-- The certificate's marked bitset is an actual pointwise octad kernel. -/
theorem native_mem_octad_kernel (i : Fin 39) (v : Fin 192) (hv : keep i v = true) :
    LinearFive.Geometry.SharpImages.markedSylow (native v) ∈ octadPointwiseKernel (octad i) := by
  apply (mem_octadPointwiseKernel _ _).mpr
  intro p hp
  change (starGroupEquivM24 (native v).val : Equiv.Perm (Fin 24)) p = p
  rw [starGroupEquivM24_apply]
  change StarOrderCertificate.relabel (perm (vertexIndex v) (StarOrderCertificate.relabel.symm p)) = p
  rw [← point_spec, keep_fixes i v hv p hp]
  exact StarOrderCertificate.relabel.apply_symm_apply p

end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows.SmallImages
