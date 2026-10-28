module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [221184, 229376).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B000
private theorem c221184 : checkChunk 221184 128 = true := by decide +kernel
private theorem c221312 : checkChunk 221312 128 = true := by decide +kernel
private theorem c221440 : checkChunk 221440 128 = true := by decide +kernel
private theorem c221568 : checkChunk 221568 128 = true := by decide +kernel
private theorem c221696 : checkChunk 221696 128 = true := by decide +kernel
private theorem c221824 : checkChunk 221824 128 = true := by decide +kernel
private theorem c221952 : checkChunk 221952 128 = true := by decide +kernel
private theorem c222080 : checkChunk 222080 128 = true := by decide +kernel
private theorem c222208 : checkChunk 222208 128 = true := by decide +kernel
private theorem c222336 : checkChunk 222336 128 = true := by decide +kernel
private theorem c222464 : checkChunk 222464 128 = true := by decide +kernel
private theorem c222592 : checkChunk 222592 128 = true := by decide +kernel
private theorem c222720 : checkChunk 222720 128 = true := by decide +kernel
private theorem c222848 : checkChunk 222848 128 = true := by decide +kernel
private theorem c222976 : checkChunk 222976 128 = true := by decide +kernel
private theorem c223104 : checkChunk 223104 128 = true := by decide +kernel
private theorem c223232 : checkChunk 223232 128 = true := by decide +kernel
private theorem c223360 : checkChunk 223360 128 = true := by decide +kernel
private theorem c223488 : checkChunk 223488 128 = true := by decide +kernel
private theorem c223616 : checkChunk 223616 128 = true := by decide +kernel
private theorem c223744 : checkChunk 223744 128 = true := by decide +kernel
private theorem c223872 : checkChunk 223872 128 = true := by decide +kernel
private theorem c224000 : checkChunk 224000 128 = true := by decide +kernel
private theorem c224128 : checkChunk 224128 128 = true := by decide +kernel
private theorem c224256 : checkChunk 224256 128 = true := by decide +kernel
private theorem c224384 : checkChunk 224384 128 = true := by decide +kernel
private theorem c224512 : checkChunk 224512 128 = true := by decide +kernel
private theorem c224640 : checkChunk 224640 128 = true := by decide +kernel
private theorem c224768 : checkChunk 224768 128 = true := by decide +kernel
private theorem c224896 : checkChunk 224896 128 = true := by decide +kernel
private theorem c225024 : checkChunk 225024 128 = true := by decide +kernel
private theorem c225152 : checkChunk 225152 128 = true := by decide +kernel
private theorem c225280 : checkChunk 225280 128 = true := by decide +kernel
private theorem c225408 : checkChunk 225408 128 = true := by decide +kernel
private theorem c225536 : checkChunk 225536 128 = true := by decide +kernel
private theorem c225664 : checkChunk 225664 128 = true := by decide +kernel
private theorem c225792 : checkChunk 225792 128 = true := by decide +kernel
private theorem c225920 : checkChunk 225920 128 = true := by decide +kernel
private theorem c226048 : checkChunk 226048 128 = true := by decide +kernel
private theorem c226176 : checkChunk 226176 128 = true := by decide +kernel
private theorem c226304 : checkChunk 226304 128 = true := by decide +kernel
private theorem c226432 : checkChunk 226432 128 = true := by decide +kernel
private theorem c226560 : checkChunk 226560 128 = true := by decide +kernel
private theorem c226688 : checkChunk 226688 128 = true := by decide +kernel
private theorem c226816 : checkChunk 226816 128 = true := by decide +kernel
private theorem c226944 : checkChunk 226944 128 = true := by decide +kernel
private theorem c227072 : checkChunk 227072 128 = true := by decide +kernel
private theorem c227200 : checkChunk 227200 128 = true := by decide +kernel
private theorem c227328 : checkChunk 227328 128 = true := by decide +kernel
private theorem c227456 : checkChunk 227456 128 = true := by decide +kernel
private theorem c227584 : checkChunk 227584 128 = true := by decide +kernel
private theorem c227712 : checkChunk 227712 128 = true := by decide +kernel
private theorem c227840 : checkChunk 227840 128 = true := by decide +kernel
private theorem c227968 : checkChunk 227968 128 = true := by decide +kernel
private theorem c228096 : checkChunk 228096 128 = true := by decide +kernel
private theorem c228224 : checkChunk 228224 128 = true := by decide +kernel
private theorem c228352 : checkChunk 228352 128 = true := by decide +kernel
private theorem c228480 : checkChunk 228480 128 = true := by decide +kernel
private theorem c228608 : checkChunk 228608 128 = true := by decide +kernel
private theorem c228736 : checkChunk 228736 128 = true := by decide +kernel
private theorem c228864 : checkChunk 228864 128 = true := by decide +kernel
private theorem c228992 : checkChunk 228992 128 = true := by decide +kernel
private theorem c229120 : checkChunk 229120 128 = true := by decide +kernel
private theorem c229248 : checkChunk 229248 128 = true := by decide +kernel

public theorem checked : Checked 221184 229376 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 221184 128 c221184) (checkChunk_sound 221312 128 c221312)) (Checked.append (checkChunk_sound 221440 128 c221440) (checkChunk_sound 221568 128 c221568))) (Checked.append (Checked.append (checkChunk_sound 221696 128 c221696) (checkChunk_sound 221824 128 c221824)) (Checked.append (checkChunk_sound 221952 128 c221952) (checkChunk_sound 222080 128 c222080)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 222208 128 c222208) (checkChunk_sound 222336 128 c222336)) (Checked.append (checkChunk_sound 222464 128 c222464) (checkChunk_sound 222592 128 c222592))) (Checked.append (Checked.append (checkChunk_sound 222720 128 c222720) (checkChunk_sound 222848 128 c222848)) (Checked.append (checkChunk_sound 222976 128 c222976) (checkChunk_sound 223104 128 c223104))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 223232 128 c223232) (checkChunk_sound 223360 128 c223360)) (Checked.append (checkChunk_sound 223488 128 c223488) (checkChunk_sound 223616 128 c223616))) (Checked.append (Checked.append (checkChunk_sound 223744 128 c223744) (checkChunk_sound 223872 128 c223872)) (Checked.append (checkChunk_sound 224000 128 c224000) (checkChunk_sound 224128 128 c224128)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 224256 128 c224256) (checkChunk_sound 224384 128 c224384)) (Checked.append (checkChunk_sound 224512 128 c224512) (checkChunk_sound 224640 128 c224640))) (Checked.append (Checked.append (checkChunk_sound 224768 128 c224768) (checkChunk_sound 224896 128 c224896)) (Checked.append (checkChunk_sound 225024 128 c225024) (checkChunk_sound 225152 128 c225152)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 225280 128 c225280) (checkChunk_sound 225408 128 c225408)) (Checked.append (checkChunk_sound 225536 128 c225536) (checkChunk_sound 225664 128 c225664))) (Checked.append (Checked.append (checkChunk_sound 225792 128 c225792) (checkChunk_sound 225920 128 c225920)) (Checked.append (checkChunk_sound 226048 128 c226048) (checkChunk_sound 226176 128 c226176)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 226304 128 c226304) (checkChunk_sound 226432 128 c226432)) (Checked.append (checkChunk_sound 226560 128 c226560) (checkChunk_sound 226688 128 c226688))) (Checked.append (Checked.append (checkChunk_sound 226816 128 c226816) (checkChunk_sound 226944 128 c226944)) (Checked.append (checkChunk_sound 227072 128 c227072) (checkChunk_sound 227200 128 c227200))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 227328 128 c227328) (checkChunk_sound 227456 128 c227456)) (Checked.append (checkChunk_sound 227584 128 c227584) (checkChunk_sound 227712 128 c227712))) (Checked.append (Checked.append (checkChunk_sound 227840 128 c227840) (checkChunk_sound 227968 128 c227968)) (Checked.append (checkChunk_sound 228096 128 c228096) (checkChunk_sound 228224 128 c228224)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 228352 128 c228352) (checkChunk_sound 228480 128 c228480)) (Checked.append (checkChunk_sound 228608 128 c228608) (checkChunk_sound 228736 128 c228736))) (Checked.append (Checked.append (checkChunk_sound 228864 128 c228864) (checkChunk_sound 228992 128 c228992)) (Checked.append (checkChunk_sound 229120 128 c229120) (checkChunk_sound 229248 128 c229248)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B000
