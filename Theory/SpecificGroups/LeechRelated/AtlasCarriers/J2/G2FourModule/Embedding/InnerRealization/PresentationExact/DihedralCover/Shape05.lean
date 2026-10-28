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
theorem shaped_81920 : shapeChunk 81920 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_82944 : shapeChunk 82944 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_83968 : shapeChunk 83968 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_84992 : shapeChunk 84992 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_86016 : shapeChunk 86016 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_87040 : shapeChunk 87040 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_88064 : shapeChunk 88064 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_89088 : shapeChunk 89088 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_90112 : shapeChunk 90112 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_91136 : shapeChunk 91136 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_92160 : shapeChunk 92160 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_93184 : shapeChunk 93184 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_94208 : shapeChunk 94208 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_95232 : shapeChunk 95232 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_96256 : shapeChunk 96256 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_97280 : shapeChunk 97280 1024 = true := by
  decide +kernel

theorem shapes_81920 (n : Nat) (hlo : 81920 ≤ n) (hhi : n < 98304) : shapeAt n = true := by
  by_cases h81920 : n < 82944
  · exact shapeChunk_sound shaped_81920 n (by omega) h81920
  by_cases h82944 : n < 83968
  · exact shapeChunk_sound shaped_82944 n (by omega) h82944
  by_cases h83968 : n < 84992
  · exact shapeChunk_sound shaped_83968 n (by omega) h83968
  by_cases h84992 : n < 86016
  · exact shapeChunk_sound shaped_84992 n (by omega) h84992
  by_cases h86016 : n < 87040
  · exact shapeChunk_sound shaped_86016 n (by omega) h86016
  by_cases h87040 : n < 88064
  · exact shapeChunk_sound shaped_87040 n (by omega) h87040
  by_cases h88064 : n < 89088
  · exact shapeChunk_sound shaped_88064 n (by omega) h88064
  by_cases h89088 : n < 90112
  · exact shapeChunk_sound shaped_89088 n (by omega) h89088
  by_cases h90112 : n < 91136
  · exact shapeChunk_sound shaped_90112 n (by omega) h90112
  by_cases h91136 : n < 92160
  · exact shapeChunk_sound shaped_91136 n (by omega) h91136
  by_cases h92160 : n < 93184
  · exact shapeChunk_sound shaped_92160 n (by omega) h92160
  by_cases h93184 : n < 94208
  · exact shapeChunk_sound shaped_93184 n (by omega) h93184
  by_cases h94208 : n < 95232
  · exact shapeChunk_sound shaped_94208 n (by omega) h94208
  by_cases h95232 : n < 96256
  · exact shapeChunk_sound shaped_95232 n (by omega) h95232
  by_cases h96256 : n < 97280
  · exact shapeChunk_sound shaped_96256 n (by omega) h96256
  exact shapeChunk_sound shaped_97280 n (by omega) hhi

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
