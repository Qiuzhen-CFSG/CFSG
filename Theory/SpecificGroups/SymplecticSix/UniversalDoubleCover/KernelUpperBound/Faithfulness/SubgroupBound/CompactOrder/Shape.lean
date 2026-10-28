module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound.CompactOrder.Shape00
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound.CompactOrder.Shape01
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound.CompactOrder.Shape02
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound.CompactOrder.Shape03
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound.CompactOrder.Shape04

/-! Kernel-checked deductions for the literal compact ATLAS S62G1-P1 subgroup presentation.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound.CompactOrder
open Subgroup.CosetWordCertificate

set_option Elab.async false

theorem all_shapes (n : Nat) (hn : n < 80640) : shapeAt n = true := by
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
  by_cases h31744 : n < 32768
  · exact shapeChunk_sound shaped_31744 n (by omega) h31744
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
  by_cases h48128 : n < 49152
  · exact shapeChunk_sound shaped_48128 n (by omega) h48128
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
  by_cases h64512 : n < 65536
  · exact shapeChunk_sound shaped_64512 n (by omega) h64512
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
  exact shapeChunk_sound shaped_79872 n (by omega) hn

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound.CompactOrder
