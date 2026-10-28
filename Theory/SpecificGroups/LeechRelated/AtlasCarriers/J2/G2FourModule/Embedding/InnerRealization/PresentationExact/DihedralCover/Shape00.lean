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
theorem shaped_0 : shapeChunk 0 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_1024 : shapeChunk 1024 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_2048 : shapeChunk 2048 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_3072 : shapeChunk 3072 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_4096 : shapeChunk 4096 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_5120 : shapeChunk 5120 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_6144 : shapeChunk 6144 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_7168 : shapeChunk 7168 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_8192 : shapeChunk 8192 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_9216 : shapeChunk 9216 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_10240 : shapeChunk 10240 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_11264 : shapeChunk 11264 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_12288 : shapeChunk 12288 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_13312 : shapeChunk 13312 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_14336 : shapeChunk 14336 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_15360 : shapeChunk 15360 1024 = true := by
  decide +kernel

theorem shapes_0 (n : Nat) (hlo : 0 ≤ n) (hhi : n < 16384) : shapeAt n = true := by
  by_cases h0 : n < 1024
  · exact shapeChunk_sound shaped_0 n (by omega) h0
  by_cases h1024 : n < 2048
  · exact shapeChunk_sound shaped_1024 n (by omega) h1024
  by_cases h2048 : n < 3072
  · exact shapeChunk_sound shaped_2048 n (by omega) h2048
  by_cases h3072 : n < 4096
  · exact shapeChunk_sound shaped_3072 n (by omega) h3072
  by_cases h4096 : n < 5120
  · exact shapeChunk_sound shaped_4096 n (by omega) h4096
  by_cases h5120 : n < 6144
  · exact shapeChunk_sound shaped_5120 n (by omega) h5120
  by_cases h6144 : n < 7168
  · exact shapeChunk_sound shaped_6144 n (by omega) h6144
  by_cases h7168 : n < 8192
  · exact shapeChunk_sound shaped_7168 n (by omega) h7168
  by_cases h8192 : n < 9216
  · exact shapeChunk_sound shaped_8192 n (by omega) h8192
  by_cases h9216 : n < 10240
  · exact shapeChunk_sound shaped_9216 n (by omega) h9216
  by_cases h10240 : n < 11264
  · exact shapeChunk_sound shaped_10240 n (by omega) h10240
  by_cases h11264 : n < 12288
  · exact shapeChunk_sound shaped_11264 n (by omega) h11264
  by_cases h12288 : n < 13312
  · exact shapeChunk_sound shaped_12288 n (by omega) h12288
  by_cases h13312 : n < 14336
  · exact shapeChunk_sound shaped_13312 n (by omega) h13312
  by_cases h14336 : n < 15360
  · exact shapeChunk_sound shaped_14336 n (by omega) h14336
  exact shapeChunk_sound shaped_15360 n (by omega) hhi

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
