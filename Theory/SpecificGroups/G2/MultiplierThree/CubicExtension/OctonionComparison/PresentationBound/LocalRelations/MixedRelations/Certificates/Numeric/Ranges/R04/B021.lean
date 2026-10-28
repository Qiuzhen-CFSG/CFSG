module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1032192, 1040384).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B021
private theorem c1032192 : checkChunk 1032192 128 = true := by decide +kernel
private theorem c1032320 : checkChunk 1032320 128 = true := by decide +kernel
private theorem c1032448 : checkChunk 1032448 128 = true := by decide +kernel
private theorem c1032576 : checkChunk 1032576 128 = true := by decide +kernel
private theorem c1032704 : checkChunk 1032704 128 = true := by decide +kernel
private theorem c1032832 : checkChunk 1032832 128 = true := by decide +kernel
private theorem c1032960 : checkChunk 1032960 128 = true := by decide +kernel
private theorem c1033088 : checkChunk 1033088 128 = true := by decide +kernel
private theorem c1033216 : checkChunk 1033216 128 = true := by decide +kernel
private theorem c1033344 : checkChunk 1033344 128 = true := by decide +kernel
private theorem c1033472 : checkChunk 1033472 128 = true := by decide +kernel
private theorem c1033600 : checkChunk 1033600 128 = true := by decide +kernel
private theorem c1033728 : checkChunk 1033728 128 = true := by decide +kernel
private theorem c1033856 : checkChunk 1033856 128 = true := by decide +kernel
private theorem c1033984 : checkChunk 1033984 128 = true := by decide +kernel
private theorem c1034112 : checkChunk 1034112 128 = true := by decide +kernel
private theorem c1034240 : checkChunk 1034240 128 = true := by decide +kernel
private theorem c1034368 : checkChunk 1034368 128 = true := by decide +kernel
private theorem c1034496 : checkChunk 1034496 128 = true := by decide +kernel
private theorem c1034624 : checkChunk 1034624 128 = true := by decide +kernel
private theorem c1034752 : checkChunk 1034752 128 = true := by decide +kernel
private theorem c1034880 : checkChunk 1034880 128 = true := by decide +kernel
private theorem c1035008 : checkChunk 1035008 128 = true := by decide +kernel
private theorem c1035136 : checkChunk 1035136 128 = true := by decide +kernel
private theorem c1035264 : checkChunk 1035264 128 = true := by decide +kernel
private theorem c1035392 : checkChunk 1035392 128 = true := by decide +kernel
private theorem c1035520 : checkChunk 1035520 128 = true := by decide +kernel
private theorem c1035648 : checkChunk 1035648 128 = true := by decide +kernel
private theorem c1035776 : checkChunk 1035776 128 = true := by decide +kernel
private theorem c1035904 : checkChunk 1035904 128 = true := by decide +kernel
private theorem c1036032 : checkChunk 1036032 128 = true := by decide +kernel
private theorem c1036160 : checkChunk 1036160 128 = true := by decide +kernel
private theorem c1036288 : checkChunk 1036288 128 = true := by decide +kernel
private theorem c1036416 : checkChunk 1036416 128 = true := by decide +kernel
private theorem c1036544 : checkChunk 1036544 128 = true := by decide +kernel
private theorem c1036672 : checkChunk 1036672 128 = true := by decide +kernel
private theorem c1036800 : checkChunk 1036800 128 = true := by decide +kernel
private theorem c1036928 : checkChunk 1036928 128 = true := by decide +kernel
private theorem c1037056 : checkChunk 1037056 128 = true := by decide +kernel
private theorem c1037184 : checkChunk 1037184 128 = true := by decide +kernel
private theorem c1037312 : checkChunk 1037312 128 = true := by decide +kernel
private theorem c1037440 : checkChunk 1037440 128 = true := by decide +kernel
private theorem c1037568 : checkChunk 1037568 128 = true := by decide +kernel
private theorem c1037696 : checkChunk 1037696 128 = true := by decide +kernel
private theorem c1037824 : checkChunk 1037824 128 = true := by decide +kernel
private theorem c1037952 : checkChunk 1037952 128 = true := by decide +kernel
private theorem c1038080 : checkChunk 1038080 128 = true := by decide +kernel
private theorem c1038208 : checkChunk 1038208 128 = true := by decide +kernel
private theorem c1038336 : checkChunk 1038336 128 = true := by decide +kernel
private theorem c1038464 : checkChunk 1038464 128 = true := by decide +kernel
private theorem c1038592 : checkChunk 1038592 128 = true := by decide +kernel
private theorem c1038720 : checkChunk 1038720 128 = true := by decide +kernel
private theorem c1038848 : checkChunk 1038848 128 = true := by decide +kernel
private theorem c1038976 : checkChunk 1038976 128 = true := by decide +kernel
private theorem c1039104 : checkChunk 1039104 128 = true := by decide +kernel
private theorem c1039232 : checkChunk 1039232 128 = true := by decide +kernel
private theorem c1039360 : checkChunk 1039360 128 = true := by decide +kernel
private theorem c1039488 : checkChunk 1039488 128 = true := by decide +kernel
private theorem c1039616 : checkChunk 1039616 128 = true := by decide +kernel
private theorem c1039744 : checkChunk 1039744 128 = true := by decide +kernel
private theorem c1039872 : checkChunk 1039872 128 = true := by decide +kernel
private theorem c1040000 : checkChunk 1040000 128 = true := by decide +kernel
private theorem c1040128 : checkChunk 1040128 128 = true := by decide +kernel
private theorem c1040256 : checkChunk 1040256 128 = true := by decide +kernel

public theorem checked : Checked 1032192 1040384 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1032192 128 c1032192) (checkChunk_sound 1032320 128 c1032320)) (Checked.append (checkChunk_sound 1032448 128 c1032448) (checkChunk_sound 1032576 128 c1032576))) (Checked.append (Checked.append (checkChunk_sound 1032704 128 c1032704) (checkChunk_sound 1032832 128 c1032832)) (Checked.append (checkChunk_sound 1032960 128 c1032960) (checkChunk_sound 1033088 128 c1033088)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1033216 128 c1033216) (checkChunk_sound 1033344 128 c1033344)) (Checked.append (checkChunk_sound 1033472 128 c1033472) (checkChunk_sound 1033600 128 c1033600))) (Checked.append (Checked.append (checkChunk_sound 1033728 128 c1033728) (checkChunk_sound 1033856 128 c1033856)) (Checked.append (checkChunk_sound 1033984 128 c1033984) (checkChunk_sound 1034112 128 c1034112))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1034240 128 c1034240) (checkChunk_sound 1034368 128 c1034368)) (Checked.append (checkChunk_sound 1034496 128 c1034496) (checkChunk_sound 1034624 128 c1034624))) (Checked.append (Checked.append (checkChunk_sound 1034752 128 c1034752) (checkChunk_sound 1034880 128 c1034880)) (Checked.append (checkChunk_sound 1035008 128 c1035008) (checkChunk_sound 1035136 128 c1035136)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1035264 128 c1035264) (checkChunk_sound 1035392 128 c1035392)) (Checked.append (checkChunk_sound 1035520 128 c1035520) (checkChunk_sound 1035648 128 c1035648))) (Checked.append (Checked.append (checkChunk_sound 1035776 128 c1035776) (checkChunk_sound 1035904 128 c1035904)) (Checked.append (checkChunk_sound 1036032 128 c1036032) (checkChunk_sound 1036160 128 c1036160)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1036288 128 c1036288) (checkChunk_sound 1036416 128 c1036416)) (Checked.append (checkChunk_sound 1036544 128 c1036544) (checkChunk_sound 1036672 128 c1036672))) (Checked.append (Checked.append (checkChunk_sound 1036800 128 c1036800) (checkChunk_sound 1036928 128 c1036928)) (Checked.append (checkChunk_sound 1037056 128 c1037056) (checkChunk_sound 1037184 128 c1037184)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1037312 128 c1037312) (checkChunk_sound 1037440 128 c1037440)) (Checked.append (checkChunk_sound 1037568 128 c1037568) (checkChunk_sound 1037696 128 c1037696))) (Checked.append (Checked.append (checkChunk_sound 1037824 128 c1037824) (checkChunk_sound 1037952 128 c1037952)) (Checked.append (checkChunk_sound 1038080 128 c1038080) (checkChunk_sound 1038208 128 c1038208))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1038336 128 c1038336) (checkChunk_sound 1038464 128 c1038464)) (Checked.append (checkChunk_sound 1038592 128 c1038592) (checkChunk_sound 1038720 128 c1038720))) (Checked.append (Checked.append (checkChunk_sound 1038848 128 c1038848) (checkChunk_sound 1038976 128 c1038976)) (Checked.append (checkChunk_sound 1039104 128 c1039104) (checkChunk_sound 1039232 128 c1039232)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1039360 128 c1039360) (checkChunk_sound 1039488 128 c1039488)) (Checked.append (checkChunk_sound 1039616 128 c1039616) (checkChunk_sound 1039744 128 c1039744))) (Checked.append (Checked.append (checkChunk_sound 1039872 128 c1039872) (checkChunk_sound 1040000 128 c1040000)) (Checked.append (checkChunk_sound 1040128 128 c1040128) (checkChunk_sound 1040256 128 c1040256)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B021
