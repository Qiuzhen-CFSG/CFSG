module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Output

/-! Output-shape checks for the literal ATLAS J2G1-P2 dihedral coset certificate.
Kernel reduction checks the selected fact's source, signed letter, and destination.
The chunk soundness theorem combines these finite checks; validity of the selected
deductions is proved separately. See `source/README.md` for the source and contract.
Sequential declarations bound the reduction cache. -/

public section
namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem shaped_98304 : shapeChunk 98304 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_99328 : shapeChunk 99328 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_100352 : shapeChunk 100352 448 = true := by
  decide +kernel

theorem shapes_98304 (n : Nat) (hlo : 98304 ≤ n) (hhi : n < 100800) : shapeAt n = true := by
  by_cases h98304 : n < 99328
  · exact shapeChunk_sound shaped_98304 n (by omega) h98304
  by_cases h99328 : n < 100352
  · exact shapeChunk_sound shaped_99328 n (by omega) h99328
  exact shapeChunk_sound shaped_100352 n (by omega) hhi

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
