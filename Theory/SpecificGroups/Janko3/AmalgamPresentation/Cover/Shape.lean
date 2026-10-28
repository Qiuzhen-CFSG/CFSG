module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape000
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape001
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape002
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape003
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape004
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape005
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape006
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape007
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape008
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape009
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape010
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape011
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape012
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape013
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape014
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape015
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape016
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape017
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape018
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape019
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape020
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape021
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape022
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape023
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape024
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape025
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape026
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Shape027

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

theorem all_shapes (n : Nat) (hn : n < 221616) : shapeAt n = true := by
  by_cases h0 : n < 8192
  · exact shapes_0 n (by omega) h0
  by_cases h8192 : n < 16384
  · exact shapes_8192 n (by omega) h8192
  by_cases h16384 : n < 24576
  · exact shapes_16384 n (by omega) h16384
  by_cases h24576 : n < 32768
  · exact shapes_24576 n (by omega) h24576
  by_cases h32768 : n < 40960
  · exact shapes_32768 n (by omega) h32768
  by_cases h40960 : n < 49152
  · exact shapes_40960 n (by omega) h40960
  by_cases h49152 : n < 57344
  · exact shapes_49152 n (by omega) h49152
  by_cases h57344 : n < 65536
  · exact shapes_57344 n (by omega) h57344
  by_cases h65536 : n < 73728
  · exact shapes_65536 n (by omega) h65536
  by_cases h73728 : n < 81920
  · exact shapes_73728 n (by omega) h73728
  by_cases h81920 : n < 90112
  · exact shapes_81920 n (by omega) h81920
  by_cases h90112 : n < 98304
  · exact shapes_90112 n (by omega) h90112
  by_cases h98304 : n < 106496
  · exact shapes_98304 n (by omega) h98304
  by_cases h106496 : n < 114688
  · exact shapes_106496 n (by omega) h106496
  by_cases h114688 : n < 122880
  · exact shapes_114688 n (by omega) h114688
  by_cases h122880 : n < 131072
  · exact shapes_122880 n (by omega) h122880
  by_cases h131072 : n < 139264
  · exact shapes_131072 n (by omega) h131072
  by_cases h139264 : n < 147456
  · exact shapes_139264 n (by omega) h139264
  by_cases h147456 : n < 155648
  · exact shapes_147456 n (by omega) h147456
  by_cases h155648 : n < 163840
  · exact shapes_155648 n (by omega) h155648
  by_cases h163840 : n < 172032
  · exact shapes_163840 n (by omega) h163840
  by_cases h172032 : n < 180224
  · exact shapes_172032 n (by omega) h172032
  by_cases h180224 : n < 188416
  · exact shapes_180224 n (by omega) h180224
  by_cases h188416 : n < 196608
  · exact shapes_188416 n (by omega) h188416
  by_cases h196608 : n < 204800
  · exact shapes_196608 n (by omega) h196608
  by_cases h204800 : n < 212992
  · exact shapes_204800 n (by omega) h204800
  by_cases h212992 : n < 221184
  · exact shapes_212992 n (by omega) h212992
  exact shapes_221184 n (by omega) hn

end Sporadic.Janko3.AmalgamPresentation.Cover
