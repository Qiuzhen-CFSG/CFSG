module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [876544, 884736).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B002
private theorem c876544 : checkChunk 876544 128 = true := by decide +kernel
private theorem c876672 : checkChunk 876672 128 = true := by decide +kernel
private theorem c876800 : checkChunk 876800 128 = true := by decide +kernel
private theorem c876928 : checkChunk 876928 128 = true := by decide +kernel
private theorem c877056 : checkChunk 877056 128 = true := by decide +kernel
private theorem c877184 : checkChunk 877184 128 = true := by decide +kernel
private theorem c877312 : checkChunk 877312 128 = true := by decide +kernel
private theorem c877440 : checkChunk 877440 128 = true := by decide +kernel
private theorem c877568 : checkChunk 877568 128 = true := by decide +kernel
private theorem c877696 : checkChunk 877696 128 = true := by decide +kernel
private theorem c877824 : checkChunk 877824 128 = true := by decide +kernel
private theorem c877952 : checkChunk 877952 128 = true := by decide +kernel
private theorem c878080 : checkChunk 878080 128 = true := by decide +kernel
private theorem c878208 : checkChunk 878208 128 = true := by decide +kernel
private theorem c878336 : checkChunk 878336 128 = true := by decide +kernel
private theorem c878464 : checkChunk 878464 128 = true := by decide +kernel
private theorem c878592 : checkChunk 878592 128 = true := by decide +kernel
private theorem c878720 : checkChunk 878720 128 = true := by decide +kernel
private theorem c878848 : checkChunk 878848 128 = true := by decide +kernel
private theorem c878976 : checkChunk 878976 128 = true := by decide +kernel
private theorem c879104 : checkChunk 879104 128 = true := by decide +kernel
private theorem c879232 : checkChunk 879232 128 = true := by decide +kernel
private theorem c879360 : checkChunk 879360 128 = true := by decide +kernel
private theorem c879488 : checkChunk 879488 128 = true := by decide +kernel
private theorem c879616 : checkChunk 879616 128 = true := by decide +kernel
private theorem c879744 : checkChunk 879744 128 = true := by decide +kernel
private theorem c879872 : checkChunk 879872 128 = true := by decide +kernel
private theorem c880000 : checkChunk 880000 128 = true := by decide +kernel
private theorem c880128 : checkChunk 880128 128 = true := by decide +kernel
private theorem c880256 : checkChunk 880256 128 = true := by decide +kernel
private theorem c880384 : checkChunk 880384 128 = true := by decide +kernel
private theorem c880512 : checkChunk 880512 128 = true := by decide +kernel
private theorem c880640 : checkChunk 880640 128 = true := by decide +kernel
private theorem c880768 : checkChunk 880768 128 = true := by decide +kernel
private theorem c880896 : checkChunk 880896 128 = true := by decide +kernel
private theorem c881024 : checkChunk 881024 128 = true := by decide +kernel
private theorem c881152 : checkChunk 881152 128 = true := by decide +kernel
private theorem c881280 : checkChunk 881280 128 = true := by decide +kernel
private theorem c881408 : checkChunk 881408 128 = true := by decide +kernel
private theorem c881536 : checkChunk 881536 128 = true := by decide +kernel
private theorem c881664 : checkChunk 881664 128 = true := by decide +kernel
private theorem c881792 : checkChunk 881792 128 = true := by decide +kernel
private theorem c881920 : checkChunk 881920 128 = true := by decide +kernel
private theorem c882048 : checkChunk 882048 128 = true := by decide +kernel
private theorem c882176 : checkChunk 882176 128 = true := by decide +kernel
private theorem c882304 : checkChunk 882304 128 = true := by decide +kernel
private theorem c882432 : checkChunk 882432 128 = true := by decide +kernel
private theorem c882560 : checkChunk 882560 128 = true := by decide +kernel
private theorem c882688 : checkChunk 882688 128 = true := by decide +kernel
private theorem c882816 : checkChunk 882816 128 = true := by decide +kernel
private theorem c882944 : checkChunk 882944 128 = true := by decide +kernel
private theorem c883072 : checkChunk 883072 128 = true := by decide +kernel
private theorem c883200 : checkChunk 883200 128 = true := by decide +kernel
private theorem c883328 : checkChunk 883328 128 = true := by decide +kernel
private theorem c883456 : checkChunk 883456 128 = true := by decide +kernel
private theorem c883584 : checkChunk 883584 128 = true := by decide +kernel
private theorem c883712 : checkChunk 883712 128 = true := by decide +kernel
private theorem c883840 : checkChunk 883840 128 = true := by decide +kernel
private theorem c883968 : checkChunk 883968 128 = true := by decide +kernel
private theorem c884096 : checkChunk 884096 128 = true := by decide +kernel
private theorem c884224 : checkChunk 884224 128 = true := by decide +kernel
private theorem c884352 : checkChunk 884352 128 = true := by decide +kernel
private theorem c884480 : checkChunk 884480 128 = true := by decide +kernel
private theorem c884608 : checkChunk 884608 128 = true := by decide +kernel

public theorem checked : Checked 876544 884736 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 876544 128 c876544) (checkChunk_sound 876672 128 c876672)) (Checked.append (checkChunk_sound 876800 128 c876800) (checkChunk_sound 876928 128 c876928))) (Checked.append (Checked.append (checkChunk_sound 877056 128 c877056) (checkChunk_sound 877184 128 c877184)) (Checked.append (checkChunk_sound 877312 128 c877312) (checkChunk_sound 877440 128 c877440)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 877568 128 c877568) (checkChunk_sound 877696 128 c877696)) (Checked.append (checkChunk_sound 877824 128 c877824) (checkChunk_sound 877952 128 c877952))) (Checked.append (Checked.append (checkChunk_sound 878080 128 c878080) (checkChunk_sound 878208 128 c878208)) (Checked.append (checkChunk_sound 878336 128 c878336) (checkChunk_sound 878464 128 c878464))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 878592 128 c878592) (checkChunk_sound 878720 128 c878720)) (Checked.append (checkChunk_sound 878848 128 c878848) (checkChunk_sound 878976 128 c878976))) (Checked.append (Checked.append (checkChunk_sound 879104 128 c879104) (checkChunk_sound 879232 128 c879232)) (Checked.append (checkChunk_sound 879360 128 c879360) (checkChunk_sound 879488 128 c879488)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 879616 128 c879616) (checkChunk_sound 879744 128 c879744)) (Checked.append (checkChunk_sound 879872 128 c879872) (checkChunk_sound 880000 128 c880000))) (Checked.append (Checked.append (checkChunk_sound 880128 128 c880128) (checkChunk_sound 880256 128 c880256)) (Checked.append (checkChunk_sound 880384 128 c880384) (checkChunk_sound 880512 128 c880512)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 880640 128 c880640) (checkChunk_sound 880768 128 c880768)) (Checked.append (checkChunk_sound 880896 128 c880896) (checkChunk_sound 881024 128 c881024))) (Checked.append (Checked.append (checkChunk_sound 881152 128 c881152) (checkChunk_sound 881280 128 c881280)) (Checked.append (checkChunk_sound 881408 128 c881408) (checkChunk_sound 881536 128 c881536)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 881664 128 c881664) (checkChunk_sound 881792 128 c881792)) (Checked.append (checkChunk_sound 881920 128 c881920) (checkChunk_sound 882048 128 c882048))) (Checked.append (Checked.append (checkChunk_sound 882176 128 c882176) (checkChunk_sound 882304 128 c882304)) (Checked.append (checkChunk_sound 882432 128 c882432) (checkChunk_sound 882560 128 c882560))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 882688 128 c882688) (checkChunk_sound 882816 128 c882816)) (Checked.append (checkChunk_sound 882944 128 c882944) (checkChunk_sound 883072 128 c883072))) (Checked.append (Checked.append (checkChunk_sound 883200 128 c883200) (checkChunk_sound 883328 128 c883328)) (Checked.append (checkChunk_sound 883456 128 c883456) (checkChunk_sound 883584 128 c883584)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 883712 128 c883712) (checkChunk_sound 883840 128 c883840)) (Checked.append (checkChunk_sound 883968 128 c883968) (checkChunk_sound 884096 128 c884096))) (Checked.append (Checked.append (checkChunk_sound 884224 128 c884224) (checkChunk_sound 884352 128 c884352)) (Checked.append (checkChunk_sound 884480 128 c884480) (checkChunk_sound 884608 128 c884608)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B002
