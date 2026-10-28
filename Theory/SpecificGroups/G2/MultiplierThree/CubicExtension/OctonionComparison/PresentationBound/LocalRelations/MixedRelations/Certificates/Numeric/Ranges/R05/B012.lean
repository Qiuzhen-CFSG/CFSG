module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1171456, 1179648).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B012
private theorem c1171456 : checkChunk 1171456 128 = true := by decide +kernel
private theorem c1171584 : checkChunk 1171584 128 = true := by decide +kernel
private theorem c1171712 : checkChunk 1171712 128 = true := by decide +kernel
private theorem c1171840 : checkChunk 1171840 128 = true := by decide +kernel
private theorem c1171968 : checkChunk 1171968 128 = true := by decide +kernel
private theorem c1172096 : checkChunk 1172096 128 = true := by decide +kernel
private theorem c1172224 : checkChunk 1172224 128 = true := by decide +kernel
private theorem c1172352 : checkChunk 1172352 128 = true := by decide +kernel
private theorem c1172480 : checkChunk 1172480 128 = true := by decide +kernel
private theorem c1172608 : checkChunk 1172608 128 = true := by decide +kernel
private theorem c1172736 : checkChunk 1172736 128 = true := by decide +kernel
private theorem c1172864 : checkChunk 1172864 128 = true := by decide +kernel
private theorem c1172992 : checkChunk 1172992 128 = true := by decide +kernel
private theorem c1173120 : checkChunk 1173120 128 = true := by decide +kernel
private theorem c1173248 : checkChunk 1173248 128 = true := by decide +kernel
private theorem c1173376 : checkChunk 1173376 128 = true := by decide +kernel
private theorem c1173504 : checkChunk 1173504 128 = true := by decide +kernel
private theorem c1173632 : checkChunk 1173632 128 = true := by decide +kernel
private theorem c1173760 : checkChunk 1173760 128 = true := by decide +kernel
private theorem c1173888 : checkChunk 1173888 128 = true := by decide +kernel
private theorem c1174016 : checkChunk 1174016 128 = true := by decide +kernel
private theorem c1174144 : checkChunk 1174144 128 = true := by decide +kernel
private theorem c1174272 : checkChunk 1174272 128 = true := by decide +kernel
private theorem c1174400 : checkChunk 1174400 128 = true := by decide +kernel
private theorem c1174528 : checkChunk 1174528 128 = true := by decide +kernel
private theorem c1174656 : checkChunk 1174656 128 = true := by decide +kernel
private theorem c1174784 : checkChunk 1174784 128 = true := by decide +kernel
private theorem c1174912 : checkChunk 1174912 128 = true := by decide +kernel
private theorem c1175040 : checkChunk 1175040 128 = true := by decide +kernel
private theorem c1175168 : checkChunk 1175168 128 = true := by decide +kernel
private theorem c1175296 : checkChunk 1175296 128 = true := by decide +kernel
private theorem c1175424 : checkChunk 1175424 128 = true := by decide +kernel
private theorem c1175552 : checkChunk 1175552 128 = true := by decide +kernel
private theorem c1175680 : checkChunk 1175680 128 = true := by decide +kernel
private theorem c1175808 : checkChunk 1175808 128 = true := by decide +kernel
private theorem c1175936 : checkChunk 1175936 128 = true := by decide +kernel
private theorem c1176064 : checkChunk 1176064 128 = true := by decide +kernel
private theorem c1176192 : checkChunk 1176192 128 = true := by decide +kernel
private theorem c1176320 : checkChunk 1176320 128 = true := by decide +kernel
private theorem c1176448 : checkChunk 1176448 128 = true := by decide +kernel
private theorem c1176576 : checkChunk 1176576 128 = true := by decide +kernel
private theorem c1176704 : checkChunk 1176704 128 = true := by decide +kernel
private theorem c1176832 : checkChunk 1176832 128 = true := by decide +kernel
private theorem c1176960 : checkChunk 1176960 128 = true := by decide +kernel
private theorem c1177088 : checkChunk 1177088 128 = true := by decide +kernel
private theorem c1177216 : checkChunk 1177216 128 = true := by decide +kernel
private theorem c1177344 : checkChunk 1177344 128 = true := by decide +kernel
private theorem c1177472 : checkChunk 1177472 128 = true := by decide +kernel
private theorem c1177600 : checkChunk 1177600 128 = true := by decide +kernel
private theorem c1177728 : checkChunk 1177728 128 = true := by decide +kernel
private theorem c1177856 : checkChunk 1177856 128 = true := by decide +kernel
private theorem c1177984 : checkChunk 1177984 128 = true := by decide +kernel
private theorem c1178112 : checkChunk 1178112 128 = true := by decide +kernel
private theorem c1178240 : checkChunk 1178240 128 = true := by decide +kernel
private theorem c1178368 : checkChunk 1178368 128 = true := by decide +kernel
private theorem c1178496 : checkChunk 1178496 128 = true := by decide +kernel
private theorem c1178624 : checkChunk 1178624 128 = true := by decide +kernel
private theorem c1178752 : checkChunk 1178752 128 = true := by decide +kernel
private theorem c1178880 : checkChunk 1178880 128 = true := by decide +kernel
private theorem c1179008 : checkChunk 1179008 128 = true := by decide +kernel
private theorem c1179136 : checkChunk 1179136 128 = true := by decide +kernel
private theorem c1179264 : checkChunk 1179264 128 = true := by decide +kernel
private theorem c1179392 : checkChunk 1179392 128 = true := by decide +kernel
private theorem c1179520 : checkChunk 1179520 128 = true := by decide +kernel

public theorem checked : Checked 1171456 1179648 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1171456 128 c1171456) (checkChunk_sound 1171584 128 c1171584)) (Checked.append (checkChunk_sound 1171712 128 c1171712) (checkChunk_sound 1171840 128 c1171840))) (Checked.append (Checked.append (checkChunk_sound 1171968 128 c1171968) (checkChunk_sound 1172096 128 c1172096)) (Checked.append (checkChunk_sound 1172224 128 c1172224) (checkChunk_sound 1172352 128 c1172352)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1172480 128 c1172480) (checkChunk_sound 1172608 128 c1172608)) (Checked.append (checkChunk_sound 1172736 128 c1172736) (checkChunk_sound 1172864 128 c1172864))) (Checked.append (Checked.append (checkChunk_sound 1172992 128 c1172992) (checkChunk_sound 1173120 128 c1173120)) (Checked.append (checkChunk_sound 1173248 128 c1173248) (checkChunk_sound 1173376 128 c1173376))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1173504 128 c1173504) (checkChunk_sound 1173632 128 c1173632)) (Checked.append (checkChunk_sound 1173760 128 c1173760) (checkChunk_sound 1173888 128 c1173888))) (Checked.append (Checked.append (checkChunk_sound 1174016 128 c1174016) (checkChunk_sound 1174144 128 c1174144)) (Checked.append (checkChunk_sound 1174272 128 c1174272) (checkChunk_sound 1174400 128 c1174400)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1174528 128 c1174528) (checkChunk_sound 1174656 128 c1174656)) (Checked.append (checkChunk_sound 1174784 128 c1174784) (checkChunk_sound 1174912 128 c1174912))) (Checked.append (Checked.append (checkChunk_sound 1175040 128 c1175040) (checkChunk_sound 1175168 128 c1175168)) (Checked.append (checkChunk_sound 1175296 128 c1175296) (checkChunk_sound 1175424 128 c1175424)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1175552 128 c1175552) (checkChunk_sound 1175680 128 c1175680)) (Checked.append (checkChunk_sound 1175808 128 c1175808) (checkChunk_sound 1175936 128 c1175936))) (Checked.append (Checked.append (checkChunk_sound 1176064 128 c1176064) (checkChunk_sound 1176192 128 c1176192)) (Checked.append (checkChunk_sound 1176320 128 c1176320) (checkChunk_sound 1176448 128 c1176448)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1176576 128 c1176576) (checkChunk_sound 1176704 128 c1176704)) (Checked.append (checkChunk_sound 1176832 128 c1176832) (checkChunk_sound 1176960 128 c1176960))) (Checked.append (Checked.append (checkChunk_sound 1177088 128 c1177088) (checkChunk_sound 1177216 128 c1177216)) (Checked.append (checkChunk_sound 1177344 128 c1177344) (checkChunk_sound 1177472 128 c1177472))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1177600 128 c1177600) (checkChunk_sound 1177728 128 c1177728)) (Checked.append (checkChunk_sound 1177856 128 c1177856) (checkChunk_sound 1177984 128 c1177984))) (Checked.append (Checked.append (checkChunk_sound 1178112 128 c1178112) (checkChunk_sound 1178240 128 c1178240)) (Checked.append (checkChunk_sound 1178368 128 c1178368) (checkChunk_sound 1178496 128 c1178496)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1178624 128 c1178624) (checkChunk_sound 1178752 128 c1178752)) (Checked.append (checkChunk_sound 1178880 128 c1178880) (checkChunk_sound 1179008 128 c1179008))) (Checked.append (Checked.append (checkChunk_sound 1179136 128 c1179136) (checkChunk_sound 1179264 128 c1179264)) (Checked.append (checkChunk_sound 1179392 128 c1179392) (checkChunk_sound 1179520 128 c1179520)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B012
