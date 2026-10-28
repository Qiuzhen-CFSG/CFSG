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
theorem shaped_16384 : shapeChunk 16384 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_17408 : shapeChunk 17408 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_18432 : shapeChunk 18432 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_19456 : shapeChunk 19456 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_20480 : shapeChunk 20480 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_21504 : shapeChunk 21504 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_22528 : shapeChunk 22528 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_23552 : shapeChunk 23552 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_24576 : shapeChunk 24576 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_25600 : shapeChunk 25600 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_26624 : shapeChunk 26624 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_27648 : shapeChunk 27648 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_28672 : shapeChunk 28672 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_29696 : shapeChunk 29696 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_30720 : shapeChunk 30720 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_31744 : shapeChunk 31744 1024 = true := by
  decide +kernel

theorem shapes_16384 (n : Nat) (hlo : 16384 ≤ n) (hhi : n < 32768) : shapeAt n = true := by
  by_cases h16384 : n < 17408
  · exact shapeChunk_sound shaped_16384 n (by omega) h16384
  by_cases h17408 : n < 18432
  · exact shapeChunk_sound shaped_17408 n (by omega) h17408
  by_cases h18432 : n < 19456
  · exact shapeChunk_sound shaped_18432 n (by omega) h18432
  by_cases h19456 : n < 20480
  · exact shapeChunk_sound shaped_19456 n (by omega) h19456
  by_cases h20480 : n < 21504
  · exact shapeChunk_sound shaped_20480 n (by omega) h20480
  by_cases h21504 : n < 22528
  · exact shapeChunk_sound shaped_21504 n (by omega) h21504
  by_cases h22528 : n < 23552
  · exact shapeChunk_sound shaped_22528 n (by omega) h22528
  by_cases h23552 : n < 24576
  · exact shapeChunk_sound shaped_23552 n (by omega) h23552
  by_cases h24576 : n < 25600
  · exact shapeChunk_sound shaped_24576 n (by omega) h24576
  by_cases h25600 : n < 26624
  · exact shapeChunk_sound shaped_25600 n (by omega) h25600
  by_cases h26624 : n < 27648
  · exact shapeChunk_sound shaped_26624 n (by omega) h26624
  by_cases h27648 : n < 28672
  · exact shapeChunk_sound shaped_27648 n (by omega) h27648
  by_cases h28672 : n < 29696
  · exact shapeChunk_sound shaped_28672 n (by omega) h28672
  by_cases h29696 : n < 30720
  · exact shapeChunk_sound shaped_29696 n (by omega) h29696
  by_cases h30720 : n < 31744
  · exact shapeChunk_sound shaped_30720 n (by omega) h30720
  exact shapeChunk_sound shaped_31744 n (by omega) hhi

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
