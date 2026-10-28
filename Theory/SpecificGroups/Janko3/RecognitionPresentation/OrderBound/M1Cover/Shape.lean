module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Shape00
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Shape01
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Shape02
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Shape03
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Shape04
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Shape05
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Shape06

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

theorem all_shapes (n : Nat) (hn : n < 24624) : shapeAt n = true := by
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
  by_cases h15360 : n < 16384
  · exact shapeChunk_sound shaped_15360 n (by omega) h15360
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
  exact shapeChunk_sound shaped_24576 n (by omega) hn

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
