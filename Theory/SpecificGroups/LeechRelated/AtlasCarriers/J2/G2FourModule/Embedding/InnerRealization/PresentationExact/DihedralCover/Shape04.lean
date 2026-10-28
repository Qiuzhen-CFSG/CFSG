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
theorem shaped_65536 : shapeChunk 65536 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_66560 : shapeChunk 66560 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_67584 : shapeChunk 67584 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_68608 : shapeChunk 68608 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_69632 : shapeChunk 69632 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_70656 : shapeChunk 70656 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_71680 : shapeChunk 71680 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_72704 : shapeChunk 72704 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_73728 : shapeChunk 73728 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_74752 : shapeChunk 74752 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_75776 : shapeChunk 75776 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_76800 : shapeChunk 76800 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_77824 : shapeChunk 77824 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_78848 : shapeChunk 78848 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_79872 : shapeChunk 79872 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_80896 : shapeChunk 80896 1024 = true := by
  decide +kernel

theorem shapes_65536 (n : Nat) (hlo : 65536 ≤ n) (hhi : n < 81920) : shapeAt n = true := by
  by_cases h65536 : n < 66560
  · exact shapeChunk_sound shaped_65536 n (by omega) h65536
  by_cases h66560 : n < 67584
  · exact shapeChunk_sound shaped_66560 n (by omega) h66560
  by_cases h67584 : n < 68608
  · exact shapeChunk_sound shaped_67584 n (by omega) h67584
  by_cases h68608 : n < 69632
  · exact shapeChunk_sound shaped_68608 n (by omega) h68608
  by_cases h69632 : n < 70656
  · exact shapeChunk_sound shaped_69632 n (by omega) h69632
  by_cases h70656 : n < 71680
  · exact shapeChunk_sound shaped_70656 n (by omega) h70656
  by_cases h71680 : n < 72704
  · exact shapeChunk_sound shaped_71680 n (by omega) h71680
  by_cases h72704 : n < 73728
  · exact shapeChunk_sound shaped_72704 n (by omega) h72704
  by_cases h73728 : n < 74752
  · exact shapeChunk_sound shaped_73728 n (by omega) h73728
  by_cases h74752 : n < 75776
  · exact shapeChunk_sound shaped_74752 n (by omega) h74752
  by_cases h75776 : n < 76800
  · exact shapeChunk_sound shaped_75776 n (by omega) h75776
  by_cases h76800 : n < 77824
  · exact shapeChunk_sound shaped_76800 n (by omega) h76800
  by_cases h77824 : n < 78848
  · exact shapeChunk_sound shaped_77824 n (by omega) h77824
  by_cases h78848 : n < 79872
  · exact shapeChunk_sound shaped_78848 n (by omega) h78848
  by_cases h79872 : n < 80896
  · exact shapeChunk_sound shaped_79872 n (by omega) h79872
  exact shapeChunk_sound shaped_80896 n (by omega) hhi

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
