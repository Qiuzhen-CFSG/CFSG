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
theorem shaped_32768 : shapeChunk 32768 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_33792 : shapeChunk 33792 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_34816 : shapeChunk 34816 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_35840 : shapeChunk 35840 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_36864 : shapeChunk 36864 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_37888 : shapeChunk 37888 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_38912 : shapeChunk 38912 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_39936 : shapeChunk 39936 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_40960 : shapeChunk 40960 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_41984 : shapeChunk 41984 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_43008 : shapeChunk 43008 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_44032 : shapeChunk 44032 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_45056 : shapeChunk 45056 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_46080 : shapeChunk 46080 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_47104 : shapeChunk 47104 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_48128 : shapeChunk 48128 1024 = true := by
  decide +kernel

theorem shapes_32768 (n : Nat) (hlo : 32768 ≤ n) (hhi : n < 49152) : shapeAt n = true := by
  by_cases h32768 : n < 33792
  · exact shapeChunk_sound shaped_32768 n (by omega) h32768
  by_cases h33792 : n < 34816
  · exact shapeChunk_sound shaped_33792 n (by omega) h33792
  by_cases h34816 : n < 35840
  · exact shapeChunk_sound shaped_34816 n (by omega) h34816
  by_cases h35840 : n < 36864
  · exact shapeChunk_sound shaped_35840 n (by omega) h35840
  by_cases h36864 : n < 37888
  · exact shapeChunk_sound shaped_36864 n (by omega) h36864
  by_cases h37888 : n < 38912
  · exact shapeChunk_sound shaped_37888 n (by omega) h37888
  by_cases h38912 : n < 39936
  · exact shapeChunk_sound shaped_38912 n (by omega) h38912
  by_cases h39936 : n < 40960
  · exact shapeChunk_sound shaped_39936 n (by omega) h39936
  by_cases h40960 : n < 41984
  · exact shapeChunk_sound shaped_40960 n (by omega) h40960
  by_cases h41984 : n < 43008
  · exact shapeChunk_sound shaped_41984 n (by omega) h41984
  by_cases h43008 : n < 44032
  · exact shapeChunk_sound shaped_43008 n (by omega) h43008
  by_cases h44032 : n < 45056
  · exact shapeChunk_sound shaped_44032 n (by omega) h44032
  by_cases h45056 : n < 46080
  · exact shapeChunk_sound shaped_45056 n (by omega) h45056
  by_cases h46080 : n < 47104
  · exact shapeChunk_sound shaped_46080 n (by omega) h46080
  by_cases h47104 : n < 48128
  · exact shapeChunk_sound shaped_47104 n (by omega) h47104
  exact shapeChunk_sound shaped_48128 n (by omega) hhi

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCertificate
