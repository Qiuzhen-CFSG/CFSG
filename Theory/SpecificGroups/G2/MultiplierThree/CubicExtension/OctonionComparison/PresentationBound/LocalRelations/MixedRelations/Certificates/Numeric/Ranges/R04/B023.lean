module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1048576, 1056768).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B023
private theorem c1048576 : checkChunk 1048576 128 = true := by decide +kernel
private theorem c1048704 : checkChunk 1048704 128 = true := by decide +kernel
private theorem c1048832 : checkChunk 1048832 128 = true := by decide +kernel
private theorem c1048960 : checkChunk 1048960 128 = true := by decide +kernel
private theorem c1049088 : checkChunk 1049088 128 = true := by decide +kernel
private theorem c1049216 : checkChunk 1049216 128 = true := by decide +kernel
private theorem c1049344 : checkChunk 1049344 128 = true := by decide +kernel
private theorem c1049472 : checkChunk 1049472 128 = true := by decide +kernel
private theorem c1049600 : checkChunk 1049600 128 = true := by decide +kernel
private theorem c1049728 : checkChunk 1049728 128 = true := by decide +kernel
private theorem c1049856 : checkChunk 1049856 128 = true := by decide +kernel
private theorem c1049984 : checkChunk 1049984 128 = true := by decide +kernel
private theorem c1050112 : checkChunk 1050112 128 = true := by decide +kernel
private theorem c1050240 : checkChunk 1050240 128 = true := by decide +kernel
private theorem c1050368 : checkChunk 1050368 128 = true := by decide +kernel
private theorem c1050496 : checkChunk 1050496 128 = true := by decide +kernel
private theorem c1050624 : checkChunk 1050624 128 = true := by decide +kernel
private theorem c1050752 : checkChunk 1050752 128 = true := by decide +kernel
private theorem c1050880 : checkChunk 1050880 128 = true := by decide +kernel
private theorem c1051008 : checkChunk 1051008 128 = true := by decide +kernel
private theorem c1051136 : checkChunk 1051136 128 = true := by decide +kernel
private theorem c1051264 : checkChunk 1051264 128 = true := by decide +kernel
private theorem c1051392 : checkChunk 1051392 128 = true := by decide +kernel
private theorem c1051520 : checkChunk 1051520 128 = true := by decide +kernel
private theorem c1051648 : checkChunk 1051648 128 = true := by decide +kernel
private theorem c1051776 : checkChunk 1051776 128 = true := by decide +kernel
private theorem c1051904 : checkChunk 1051904 128 = true := by decide +kernel
private theorem c1052032 : checkChunk 1052032 128 = true := by decide +kernel
private theorem c1052160 : checkChunk 1052160 128 = true := by decide +kernel
private theorem c1052288 : checkChunk 1052288 128 = true := by decide +kernel
private theorem c1052416 : checkChunk 1052416 128 = true := by decide +kernel
private theorem c1052544 : checkChunk 1052544 128 = true := by decide +kernel
private theorem c1052672 : checkChunk 1052672 128 = true := by decide +kernel
private theorem c1052800 : checkChunk 1052800 128 = true := by decide +kernel
private theorem c1052928 : checkChunk 1052928 128 = true := by decide +kernel
private theorem c1053056 : checkChunk 1053056 128 = true := by decide +kernel
private theorem c1053184 : checkChunk 1053184 128 = true := by decide +kernel
private theorem c1053312 : checkChunk 1053312 128 = true := by decide +kernel
private theorem c1053440 : checkChunk 1053440 128 = true := by decide +kernel
private theorem c1053568 : checkChunk 1053568 128 = true := by decide +kernel
private theorem c1053696 : checkChunk 1053696 128 = true := by decide +kernel
private theorem c1053824 : checkChunk 1053824 128 = true := by decide +kernel
private theorem c1053952 : checkChunk 1053952 128 = true := by decide +kernel
private theorem c1054080 : checkChunk 1054080 128 = true := by decide +kernel
private theorem c1054208 : checkChunk 1054208 128 = true := by decide +kernel
private theorem c1054336 : checkChunk 1054336 128 = true := by decide +kernel
private theorem c1054464 : checkChunk 1054464 128 = true := by decide +kernel
private theorem c1054592 : checkChunk 1054592 128 = true := by decide +kernel
private theorem c1054720 : checkChunk 1054720 128 = true := by decide +kernel
private theorem c1054848 : checkChunk 1054848 128 = true := by decide +kernel
private theorem c1054976 : checkChunk 1054976 128 = true := by decide +kernel
private theorem c1055104 : checkChunk 1055104 128 = true := by decide +kernel
private theorem c1055232 : checkChunk 1055232 128 = true := by decide +kernel
private theorem c1055360 : checkChunk 1055360 128 = true := by decide +kernel
private theorem c1055488 : checkChunk 1055488 128 = true := by decide +kernel
private theorem c1055616 : checkChunk 1055616 128 = true := by decide +kernel
private theorem c1055744 : checkChunk 1055744 128 = true := by decide +kernel
private theorem c1055872 : checkChunk 1055872 128 = true := by decide +kernel
private theorem c1056000 : checkChunk 1056000 128 = true := by decide +kernel
private theorem c1056128 : checkChunk 1056128 128 = true := by decide +kernel
private theorem c1056256 : checkChunk 1056256 128 = true := by decide +kernel
private theorem c1056384 : checkChunk 1056384 128 = true := by decide +kernel
private theorem c1056512 : checkChunk 1056512 128 = true := by decide +kernel
private theorem c1056640 : checkChunk 1056640 128 = true := by decide +kernel

public theorem checked : Checked 1048576 1056768 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1048576 128 c1048576) (checkChunk_sound 1048704 128 c1048704)) (Checked.append (checkChunk_sound 1048832 128 c1048832) (checkChunk_sound 1048960 128 c1048960))) (Checked.append (Checked.append (checkChunk_sound 1049088 128 c1049088) (checkChunk_sound 1049216 128 c1049216)) (Checked.append (checkChunk_sound 1049344 128 c1049344) (checkChunk_sound 1049472 128 c1049472)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1049600 128 c1049600) (checkChunk_sound 1049728 128 c1049728)) (Checked.append (checkChunk_sound 1049856 128 c1049856) (checkChunk_sound 1049984 128 c1049984))) (Checked.append (Checked.append (checkChunk_sound 1050112 128 c1050112) (checkChunk_sound 1050240 128 c1050240)) (Checked.append (checkChunk_sound 1050368 128 c1050368) (checkChunk_sound 1050496 128 c1050496))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1050624 128 c1050624) (checkChunk_sound 1050752 128 c1050752)) (Checked.append (checkChunk_sound 1050880 128 c1050880) (checkChunk_sound 1051008 128 c1051008))) (Checked.append (Checked.append (checkChunk_sound 1051136 128 c1051136) (checkChunk_sound 1051264 128 c1051264)) (Checked.append (checkChunk_sound 1051392 128 c1051392) (checkChunk_sound 1051520 128 c1051520)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1051648 128 c1051648) (checkChunk_sound 1051776 128 c1051776)) (Checked.append (checkChunk_sound 1051904 128 c1051904) (checkChunk_sound 1052032 128 c1052032))) (Checked.append (Checked.append (checkChunk_sound 1052160 128 c1052160) (checkChunk_sound 1052288 128 c1052288)) (Checked.append (checkChunk_sound 1052416 128 c1052416) (checkChunk_sound 1052544 128 c1052544)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1052672 128 c1052672) (checkChunk_sound 1052800 128 c1052800)) (Checked.append (checkChunk_sound 1052928 128 c1052928) (checkChunk_sound 1053056 128 c1053056))) (Checked.append (Checked.append (checkChunk_sound 1053184 128 c1053184) (checkChunk_sound 1053312 128 c1053312)) (Checked.append (checkChunk_sound 1053440 128 c1053440) (checkChunk_sound 1053568 128 c1053568)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1053696 128 c1053696) (checkChunk_sound 1053824 128 c1053824)) (Checked.append (checkChunk_sound 1053952 128 c1053952) (checkChunk_sound 1054080 128 c1054080))) (Checked.append (Checked.append (checkChunk_sound 1054208 128 c1054208) (checkChunk_sound 1054336 128 c1054336)) (Checked.append (checkChunk_sound 1054464 128 c1054464) (checkChunk_sound 1054592 128 c1054592))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1054720 128 c1054720) (checkChunk_sound 1054848 128 c1054848)) (Checked.append (checkChunk_sound 1054976 128 c1054976) (checkChunk_sound 1055104 128 c1055104))) (Checked.append (Checked.append (checkChunk_sound 1055232 128 c1055232) (checkChunk_sound 1055360 128 c1055360)) (Checked.append (checkChunk_sound 1055488 128 c1055488) (checkChunk_sound 1055616 128 c1055616)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1055744 128 c1055744) (checkChunk_sound 1055872 128 c1055872)) (Checked.append (checkChunk_sound 1056000 128 c1056000) (checkChunk_sound 1056128 128 c1056128))) (Checked.append (Checked.append (checkChunk_sound 1056256 128 c1056256) (checkChunk_sound 1056384 128 c1056384)) (Checked.append (checkChunk_sound 1056512 128 c1056512) (checkChunk_sound 1056640 128 c1056640)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B023
