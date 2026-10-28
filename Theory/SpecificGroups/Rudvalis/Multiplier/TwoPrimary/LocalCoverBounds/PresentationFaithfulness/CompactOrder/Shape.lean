module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactOrder.Shape00

/-! Kernel-checked deductions for the literal compact Rudvalis max4 auxiliary presentation.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Rudvalis.Multiplier.TwoPrimary.LocalPresentation.PresentationFaithfulness.CompactOrder
open Subgroup.CosetWordCertificate

set_option Elab.async false

theorem all_shapes (n : Nat) (hn : n < 11264) : shapeAt n = true := by
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
  exact shapeChunk_sound shaped_10240 n (by omega) hn

end Rudvalis.Multiplier.TwoPrimary.LocalPresentation.PresentationFaithfulness.CompactOrder
