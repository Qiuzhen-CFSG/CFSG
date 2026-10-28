module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1196032, 1204224).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B015
private theorem c1196032 : checkChunk 1196032 128 = true := by decide +kernel
private theorem c1196160 : checkChunk 1196160 128 = true := by decide +kernel
private theorem c1196288 : checkChunk 1196288 128 = true := by decide +kernel
private theorem c1196416 : checkChunk 1196416 128 = true := by decide +kernel
private theorem c1196544 : checkChunk 1196544 128 = true := by decide +kernel
private theorem c1196672 : checkChunk 1196672 128 = true := by decide +kernel
private theorem c1196800 : checkChunk 1196800 128 = true := by decide +kernel
private theorem c1196928 : checkChunk 1196928 128 = true := by decide +kernel
private theorem c1197056 : checkChunk 1197056 128 = true := by decide +kernel
private theorem c1197184 : checkChunk 1197184 128 = true := by decide +kernel
private theorem c1197312 : checkChunk 1197312 128 = true := by decide +kernel
private theorem c1197440 : checkChunk 1197440 128 = true := by decide +kernel
private theorem c1197568 : checkChunk 1197568 128 = true := by decide +kernel
private theorem c1197696 : checkChunk 1197696 128 = true := by decide +kernel
private theorem c1197824 : checkChunk 1197824 128 = true := by decide +kernel
private theorem c1197952 : checkChunk 1197952 128 = true := by decide +kernel
private theorem c1198080 : checkChunk 1198080 128 = true := by decide +kernel
private theorem c1198208 : checkChunk 1198208 128 = true := by decide +kernel
private theorem c1198336 : checkChunk 1198336 128 = true := by decide +kernel
private theorem c1198464 : checkChunk 1198464 128 = true := by decide +kernel
private theorem c1198592 : checkChunk 1198592 128 = true := by decide +kernel
private theorem c1198720 : checkChunk 1198720 128 = true := by decide +kernel
private theorem c1198848 : checkChunk 1198848 128 = true := by decide +kernel
private theorem c1198976 : checkChunk 1198976 128 = true := by decide +kernel
private theorem c1199104 : checkChunk 1199104 128 = true := by decide +kernel
private theorem c1199232 : checkChunk 1199232 128 = true := by decide +kernel
private theorem c1199360 : checkChunk 1199360 128 = true := by decide +kernel
private theorem c1199488 : checkChunk 1199488 128 = true := by decide +kernel
private theorem c1199616 : checkChunk 1199616 128 = true := by decide +kernel
private theorem c1199744 : checkChunk 1199744 128 = true := by decide +kernel
private theorem c1199872 : checkChunk 1199872 128 = true := by decide +kernel
private theorem c1200000 : checkChunk 1200000 128 = true := by decide +kernel
private theorem c1200128 : checkChunk 1200128 128 = true := by decide +kernel
private theorem c1200256 : checkChunk 1200256 128 = true := by decide +kernel
private theorem c1200384 : checkChunk 1200384 128 = true := by decide +kernel
private theorem c1200512 : checkChunk 1200512 128 = true := by decide +kernel
private theorem c1200640 : checkChunk 1200640 128 = true := by decide +kernel
private theorem c1200768 : checkChunk 1200768 128 = true := by decide +kernel
private theorem c1200896 : checkChunk 1200896 128 = true := by decide +kernel
private theorem c1201024 : checkChunk 1201024 128 = true := by decide +kernel
private theorem c1201152 : checkChunk 1201152 128 = true := by decide +kernel
private theorem c1201280 : checkChunk 1201280 128 = true := by decide +kernel
private theorem c1201408 : checkChunk 1201408 128 = true := by decide +kernel
private theorem c1201536 : checkChunk 1201536 128 = true := by decide +kernel
private theorem c1201664 : checkChunk 1201664 128 = true := by decide +kernel
private theorem c1201792 : checkChunk 1201792 128 = true := by decide +kernel
private theorem c1201920 : checkChunk 1201920 128 = true := by decide +kernel
private theorem c1202048 : checkChunk 1202048 128 = true := by decide +kernel
private theorem c1202176 : checkChunk 1202176 128 = true := by decide +kernel
private theorem c1202304 : checkChunk 1202304 128 = true := by decide +kernel
private theorem c1202432 : checkChunk 1202432 128 = true := by decide +kernel
private theorem c1202560 : checkChunk 1202560 128 = true := by decide +kernel
private theorem c1202688 : checkChunk 1202688 128 = true := by decide +kernel
private theorem c1202816 : checkChunk 1202816 128 = true := by decide +kernel
private theorem c1202944 : checkChunk 1202944 128 = true := by decide +kernel
private theorem c1203072 : checkChunk 1203072 128 = true := by decide +kernel
private theorem c1203200 : checkChunk 1203200 128 = true := by decide +kernel
private theorem c1203328 : checkChunk 1203328 128 = true := by decide +kernel
private theorem c1203456 : checkChunk 1203456 128 = true := by decide +kernel
private theorem c1203584 : checkChunk 1203584 128 = true := by decide +kernel
private theorem c1203712 : checkChunk 1203712 128 = true := by decide +kernel
private theorem c1203840 : checkChunk 1203840 128 = true := by decide +kernel
private theorem c1203968 : checkChunk 1203968 128 = true := by decide +kernel
private theorem c1204096 : checkChunk 1204096 128 = true := by decide +kernel

public theorem checked : Checked 1196032 1204224 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1196032 128 c1196032) (checkChunk_sound 1196160 128 c1196160)) (Checked.append (checkChunk_sound 1196288 128 c1196288) (checkChunk_sound 1196416 128 c1196416))) (Checked.append (Checked.append (checkChunk_sound 1196544 128 c1196544) (checkChunk_sound 1196672 128 c1196672)) (Checked.append (checkChunk_sound 1196800 128 c1196800) (checkChunk_sound 1196928 128 c1196928)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1197056 128 c1197056) (checkChunk_sound 1197184 128 c1197184)) (Checked.append (checkChunk_sound 1197312 128 c1197312) (checkChunk_sound 1197440 128 c1197440))) (Checked.append (Checked.append (checkChunk_sound 1197568 128 c1197568) (checkChunk_sound 1197696 128 c1197696)) (Checked.append (checkChunk_sound 1197824 128 c1197824) (checkChunk_sound 1197952 128 c1197952))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1198080 128 c1198080) (checkChunk_sound 1198208 128 c1198208)) (Checked.append (checkChunk_sound 1198336 128 c1198336) (checkChunk_sound 1198464 128 c1198464))) (Checked.append (Checked.append (checkChunk_sound 1198592 128 c1198592) (checkChunk_sound 1198720 128 c1198720)) (Checked.append (checkChunk_sound 1198848 128 c1198848) (checkChunk_sound 1198976 128 c1198976)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1199104 128 c1199104) (checkChunk_sound 1199232 128 c1199232)) (Checked.append (checkChunk_sound 1199360 128 c1199360) (checkChunk_sound 1199488 128 c1199488))) (Checked.append (Checked.append (checkChunk_sound 1199616 128 c1199616) (checkChunk_sound 1199744 128 c1199744)) (Checked.append (checkChunk_sound 1199872 128 c1199872) (checkChunk_sound 1200000 128 c1200000)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1200128 128 c1200128) (checkChunk_sound 1200256 128 c1200256)) (Checked.append (checkChunk_sound 1200384 128 c1200384) (checkChunk_sound 1200512 128 c1200512))) (Checked.append (Checked.append (checkChunk_sound 1200640 128 c1200640) (checkChunk_sound 1200768 128 c1200768)) (Checked.append (checkChunk_sound 1200896 128 c1200896) (checkChunk_sound 1201024 128 c1201024)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1201152 128 c1201152) (checkChunk_sound 1201280 128 c1201280)) (Checked.append (checkChunk_sound 1201408 128 c1201408) (checkChunk_sound 1201536 128 c1201536))) (Checked.append (Checked.append (checkChunk_sound 1201664 128 c1201664) (checkChunk_sound 1201792 128 c1201792)) (Checked.append (checkChunk_sound 1201920 128 c1201920) (checkChunk_sound 1202048 128 c1202048))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1202176 128 c1202176) (checkChunk_sound 1202304 128 c1202304)) (Checked.append (checkChunk_sound 1202432 128 c1202432) (checkChunk_sound 1202560 128 c1202560))) (Checked.append (Checked.append (checkChunk_sound 1202688 128 c1202688) (checkChunk_sound 1202816 128 c1202816)) (Checked.append (checkChunk_sound 1202944 128 c1202944) (checkChunk_sound 1203072 128 c1203072)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1203200 128 c1203200) (checkChunk_sound 1203328 128 c1203328)) (Checked.append (checkChunk_sound 1203456 128 c1203456) (checkChunk_sound 1203584 128 c1203584))) (Checked.append (Checked.append (checkChunk_sound 1203712 128 c1203712) (checkChunk_sound 1203840 128 c1203840)) (Checked.append (checkChunk_sound 1203968 128 c1203968) (checkChunk_sound 1204096 128 c1204096)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B015
