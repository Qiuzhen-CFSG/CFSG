module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [942080, 950272).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B010
private theorem c942080 : checkChunk 942080 128 = true := by decide +kernel
private theorem c942208 : checkChunk 942208 128 = true := by decide +kernel
private theorem c942336 : checkChunk 942336 128 = true := by decide +kernel
private theorem c942464 : checkChunk 942464 128 = true := by decide +kernel
private theorem c942592 : checkChunk 942592 128 = true := by decide +kernel
private theorem c942720 : checkChunk 942720 128 = true := by decide +kernel
private theorem c942848 : checkChunk 942848 128 = true := by decide +kernel
private theorem c942976 : checkChunk 942976 128 = true := by decide +kernel
private theorem c943104 : checkChunk 943104 128 = true := by decide +kernel
private theorem c943232 : checkChunk 943232 128 = true := by decide +kernel
private theorem c943360 : checkChunk 943360 128 = true := by decide +kernel
private theorem c943488 : checkChunk 943488 128 = true := by decide +kernel
private theorem c943616 : checkChunk 943616 128 = true := by decide +kernel
private theorem c943744 : checkChunk 943744 128 = true := by decide +kernel
private theorem c943872 : checkChunk 943872 128 = true := by decide +kernel
private theorem c944000 : checkChunk 944000 128 = true := by decide +kernel
private theorem c944128 : checkChunk 944128 128 = true := by decide +kernel
private theorem c944256 : checkChunk 944256 128 = true := by decide +kernel
private theorem c944384 : checkChunk 944384 128 = true := by decide +kernel
private theorem c944512 : checkChunk 944512 128 = true := by decide +kernel
private theorem c944640 : checkChunk 944640 128 = true := by decide +kernel
private theorem c944768 : checkChunk 944768 128 = true := by decide +kernel
private theorem c944896 : checkChunk 944896 128 = true := by decide +kernel
private theorem c945024 : checkChunk 945024 128 = true := by decide +kernel
private theorem c945152 : checkChunk 945152 128 = true := by decide +kernel
private theorem c945280 : checkChunk 945280 128 = true := by decide +kernel
private theorem c945408 : checkChunk 945408 128 = true := by decide +kernel
private theorem c945536 : checkChunk 945536 128 = true := by decide +kernel
private theorem c945664 : checkChunk 945664 128 = true := by decide +kernel
private theorem c945792 : checkChunk 945792 128 = true := by decide +kernel
private theorem c945920 : checkChunk 945920 128 = true := by decide +kernel
private theorem c946048 : checkChunk 946048 128 = true := by decide +kernel
private theorem c946176 : checkChunk 946176 128 = true := by decide +kernel
private theorem c946304 : checkChunk 946304 128 = true := by decide +kernel
private theorem c946432 : checkChunk 946432 128 = true := by decide +kernel
private theorem c946560 : checkChunk 946560 128 = true := by decide +kernel
private theorem c946688 : checkChunk 946688 128 = true := by decide +kernel
private theorem c946816 : checkChunk 946816 128 = true := by decide +kernel
private theorem c946944 : checkChunk 946944 128 = true := by decide +kernel
private theorem c947072 : checkChunk 947072 128 = true := by decide +kernel
private theorem c947200 : checkChunk 947200 128 = true := by decide +kernel
private theorem c947328 : checkChunk 947328 128 = true := by decide +kernel
private theorem c947456 : checkChunk 947456 128 = true := by decide +kernel
private theorem c947584 : checkChunk 947584 128 = true := by decide +kernel
private theorem c947712 : checkChunk 947712 128 = true := by decide +kernel
private theorem c947840 : checkChunk 947840 128 = true := by decide +kernel
private theorem c947968 : checkChunk 947968 128 = true := by decide +kernel
private theorem c948096 : checkChunk 948096 128 = true := by decide +kernel
private theorem c948224 : checkChunk 948224 128 = true := by decide +kernel
private theorem c948352 : checkChunk 948352 128 = true := by decide +kernel
private theorem c948480 : checkChunk 948480 128 = true := by decide +kernel
private theorem c948608 : checkChunk 948608 128 = true := by decide +kernel
private theorem c948736 : checkChunk 948736 128 = true := by decide +kernel
private theorem c948864 : checkChunk 948864 128 = true := by decide +kernel
private theorem c948992 : checkChunk 948992 128 = true := by decide +kernel
private theorem c949120 : checkChunk 949120 128 = true := by decide +kernel
private theorem c949248 : checkChunk 949248 128 = true := by decide +kernel
private theorem c949376 : checkChunk 949376 128 = true := by decide +kernel
private theorem c949504 : checkChunk 949504 128 = true := by decide +kernel
private theorem c949632 : checkChunk 949632 128 = true := by decide +kernel
private theorem c949760 : checkChunk 949760 128 = true := by decide +kernel
private theorem c949888 : checkChunk 949888 128 = true := by decide +kernel
private theorem c950016 : checkChunk 950016 128 = true := by decide +kernel
private theorem c950144 : checkChunk 950144 128 = true := by decide +kernel

public theorem checked : Checked 942080 950272 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 942080 128 c942080) (checkChunk_sound 942208 128 c942208)) (Checked.append (checkChunk_sound 942336 128 c942336) (checkChunk_sound 942464 128 c942464))) (Checked.append (Checked.append (checkChunk_sound 942592 128 c942592) (checkChunk_sound 942720 128 c942720)) (Checked.append (checkChunk_sound 942848 128 c942848) (checkChunk_sound 942976 128 c942976)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 943104 128 c943104) (checkChunk_sound 943232 128 c943232)) (Checked.append (checkChunk_sound 943360 128 c943360) (checkChunk_sound 943488 128 c943488))) (Checked.append (Checked.append (checkChunk_sound 943616 128 c943616) (checkChunk_sound 943744 128 c943744)) (Checked.append (checkChunk_sound 943872 128 c943872) (checkChunk_sound 944000 128 c944000))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 944128 128 c944128) (checkChunk_sound 944256 128 c944256)) (Checked.append (checkChunk_sound 944384 128 c944384) (checkChunk_sound 944512 128 c944512))) (Checked.append (Checked.append (checkChunk_sound 944640 128 c944640) (checkChunk_sound 944768 128 c944768)) (Checked.append (checkChunk_sound 944896 128 c944896) (checkChunk_sound 945024 128 c945024)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 945152 128 c945152) (checkChunk_sound 945280 128 c945280)) (Checked.append (checkChunk_sound 945408 128 c945408) (checkChunk_sound 945536 128 c945536))) (Checked.append (Checked.append (checkChunk_sound 945664 128 c945664) (checkChunk_sound 945792 128 c945792)) (Checked.append (checkChunk_sound 945920 128 c945920) (checkChunk_sound 946048 128 c946048)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 946176 128 c946176) (checkChunk_sound 946304 128 c946304)) (Checked.append (checkChunk_sound 946432 128 c946432) (checkChunk_sound 946560 128 c946560))) (Checked.append (Checked.append (checkChunk_sound 946688 128 c946688) (checkChunk_sound 946816 128 c946816)) (Checked.append (checkChunk_sound 946944 128 c946944) (checkChunk_sound 947072 128 c947072)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 947200 128 c947200) (checkChunk_sound 947328 128 c947328)) (Checked.append (checkChunk_sound 947456 128 c947456) (checkChunk_sound 947584 128 c947584))) (Checked.append (Checked.append (checkChunk_sound 947712 128 c947712) (checkChunk_sound 947840 128 c947840)) (Checked.append (checkChunk_sound 947968 128 c947968) (checkChunk_sound 948096 128 c948096))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 948224 128 c948224) (checkChunk_sound 948352 128 c948352)) (Checked.append (checkChunk_sound 948480 128 c948480) (checkChunk_sound 948608 128 c948608))) (Checked.append (Checked.append (checkChunk_sound 948736 128 c948736) (checkChunk_sound 948864 128 c948864)) (Checked.append (checkChunk_sound 948992 128 c948992) (checkChunk_sound 949120 128 c949120)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 949248 128 c949248) (checkChunk_sound 949376 128 c949376)) (Checked.append (checkChunk_sound 949504 128 c949504) (checkChunk_sound 949632 128 c949632))) (Checked.append (Checked.append (checkChunk_sound 949760 128 c949760) (checkChunk_sound 949888 128 c949888)) (Checked.append (checkChunk_sound 950016 128 c950016) (checkChunk_sound 950144 128 c950144)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B010
