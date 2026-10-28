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
theorem shaped_49152 : shapeChunk 49152 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_50176 : shapeChunk 50176 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_51200 : shapeChunk 51200 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_52224 : shapeChunk 52224 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_53248 : shapeChunk 53248 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_54272 : shapeChunk 54272 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_55296 : shapeChunk 55296 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_56320 : shapeChunk 56320 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_57344 : shapeChunk 57344 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_58368 : shapeChunk 58368 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_59392 : shapeChunk 59392 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_60416 : shapeChunk 60416 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_61440 : shapeChunk 61440 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_62464 : shapeChunk 62464 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_63488 : shapeChunk 63488 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_64512 : shapeChunk 64512 1024 = true := by
  decide +kernel

theorem shapes_49152 (n : Nat) (hlo : 49152 ≤ n) (hhi : n < 65536) : shapeAt n = true := by
  by_cases h49152 : n < 50176
  · exact shapeChunk_sound shaped_49152 n (by omega) h49152
  by_cases h50176 : n < 51200
  · exact shapeChunk_sound shaped_50176 n (by omega) h50176
  by_cases h51200 : n < 52224
  · exact shapeChunk_sound shaped_51200 n (by omega) h51200
  by_cases h52224 : n < 53248
  · exact shapeChunk_sound shaped_52224 n (by omega) h52224
  by_cases h53248 : n < 54272
  · exact shapeChunk_sound shaped_53248 n (by omega) h53248
  by_cases h54272 : n < 55296
  · exact shapeChunk_sound shaped_54272 n (by omega) h54272
  by_cases h55296 : n < 56320
  · exact shapeChunk_sound shaped_55296 n (by omega) h55296
  by_cases h56320 : n < 57344
  · exact shapeChunk_sound shaped_56320 n (by omega) h56320
  by_cases h57344 : n < 58368
  · exact shapeChunk_sound shaped_57344 n (by omega) h57344
  by_cases h58368 : n < 59392
  · exact shapeChunk_sound shaped_58368 n (by omega) h58368
  by_cases h59392 : n < 60416
  · exact shapeChunk_sound shaped_59392 n (by omega) h59392
  by_cases h60416 : n < 61440
  · exact shapeChunk_sound shaped_60416 n (by omega) h60416
  by_cases h61440 : n < 62464
  · exact shapeChunk_sound shaped_61440 n (by omega) h61440
  by_cases h62464 : n < 63488
  · exact shapeChunk_sound shaped_62464 n (by omega) h62464
  by_cases h63488 : n < 64512
  · exact shapeChunk_sound shaped_63488 n (by omega) h63488
  exact shapeChunk_sound shaped_64512 n (by omega) hhi

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
