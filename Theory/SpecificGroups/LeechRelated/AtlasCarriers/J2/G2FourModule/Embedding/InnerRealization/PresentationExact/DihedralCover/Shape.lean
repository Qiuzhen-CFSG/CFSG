module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Shape00
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Shape01
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Shape02
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Shape03
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Shape04
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Shape05
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Shape06

/-! Output-shape checks for the literal ATLAS J2G1-P2 dihedral coset certificate.
Kernel reduction checks the selected fact's source, signed letter, and destination.
The chunk soundness theorem combines these finite checks; validity of the selected
deductions is proved separately. See `source/README.md` for the source and contract.
Sequential declarations bound the reduction cache. -/

public section
namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

theorem all_shapes (n : Nat) (hn : n < 100800) : shapeAt n = true := by
  by_cases h0 : n < 16384
  · exact shapes_0 n (by omega) h0
  by_cases h16384 : n < 32768
  · exact shapes_16384 n (by omega) h16384
  by_cases h32768 : n < 49152
  · exact shapes_32768 n (by omega) h32768
  by_cases h49152 : n < 65536
  · exact shapes_49152 n (by omega) h49152
  by_cases h65536 : n < 81920
  · exact shapes_65536 n (by omega) h65536
  by_cases h81920 : n < 98304
  · exact shapes_81920 n (by omega) h81920
  exact shapes_98304 n (by omega) hn

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
