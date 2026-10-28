module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1146880, 1155072).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B009
private theorem c1146880 : checkChunk 1146880 128 = true := by decide +kernel
private theorem c1147008 : checkChunk 1147008 128 = true := by decide +kernel
private theorem c1147136 : checkChunk 1147136 128 = true := by decide +kernel
private theorem c1147264 : checkChunk 1147264 128 = true := by decide +kernel
private theorem c1147392 : checkChunk 1147392 128 = true := by decide +kernel
private theorem c1147520 : checkChunk 1147520 128 = true := by decide +kernel
private theorem c1147648 : checkChunk 1147648 128 = true := by decide +kernel
private theorem c1147776 : checkChunk 1147776 128 = true := by decide +kernel
private theorem c1147904 : checkChunk 1147904 128 = true := by decide +kernel
private theorem c1148032 : checkChunk 1148032 128 = true := by decide +kernel
private theorem c1148160 : checkChunk 1148160 128 = true := by decide +kernel
private theorem c1148288 : checkChunk 1148288 128 = true := by decide +kernel
private theorem c1148416 : checkChunk 1148416 128 = true := by decide +kernel
private theorem c1148544 : checkChunk 1148544 128 = true := by decide +kernel
private theorem c1148672 : checkChunk 1148672 128 = true := by decide +kernel
private theorem c1148800 : checkChunk 1148800 128 = true := by decide +kernel
private theorem c1148928 : checkChunk 1148928 128 = true := by decide +kernel
private theorem c1149056 : checkChunk 1149056 128 = true := by decide +kernel
private theorem c1149184 : checkChunk 1149184 128 = true := by decide +kernel
private theorem c1149312 : checkChunk 1149312 128 = true := by decide +kernel
private theorem c1149440 : checkChunk 1149440 128 = true := by decide +kernel
private theorem c1149568 : checkChunk 1149568 128 = true := by decide +kernel
private theorem c1149696 : checkChunk 1149696 128 = true := by decide +kernel
private theorem c1149824 : checkChunk 1149824 128 = true := by decide +kernel
private theorem c1149952 : checkChunk 1149952 128 = true := by decide +kernel
private theorem c1150080 : checkChunk 1150080 128 = true := by decide +kernel
private theorem c1150208 : checkChunk 1150208 128 = true := by decide +kernel
private theorem c1150336 : checkChunk 1150336 128 = true := by decide +kernel
private theorem c1150464 : checkChunk 1150464 128 = true := by decide +kernel
private theorem c1150592 : checkChunk 1150592 128 = true := by decide +kernel
private theorem c1150720 : checkChunk 1150720 128 = true := by decide +kernel
private theorem c1150848 : checkChunk 1150848 128 = true := by decide +kernel
private theorem c1150976 : checkChunk 1150976 128 = true := by decide +kernel
private theorem c1151104 : checkChunk 1151104 128 = true := by decide +kernel
private theorem c1151232 : checkChunk 1151232 128 = true := by decide +kernel
private theorem c1151360 : checkChunk 1151360 128 = true := by decide +kernel
private theorem c1151488 : checkChunk 1151488 128 = true := by decide +kernel
private theorem c1151616 : checkChunk 1151616 128 = true := by decide +kernel
private theorem c1151744 : checkChunk 1151744 128 = true := by decide +kernel
private theorem c1151872 : checkChunk 1151872 128 = true := by decide +kernel
private theorem c1152000 : checkChunk 1152000 128 = true := by decide +kernel
private theorem c1152128 : checkChunk 1152128 128 = true := by decide +kernel
private theorem c1152256 : checkChunk 1152256 128 = true := by decide +kernel
private theorem c1152384 : checkChunk 1152384 128 = true := by decide +kernel
private theorem c1152512 : checkChunk 1152512 128 = true := by decide +kernel
private theorem c1152640 : checkChunk 1152640 128 = true := by decide +kernel
private theorem c1152768 : checkChunk 1152768 128 = true := by decide +kernel
private theorem c1152896 : checkChunk 1152896 128 = true := by decide +kernel
private theorem c1153024 : checkChunk 1153024 128 = true := by decide +kernel
private theorem c1153152 : checkChunk 1153152 128 = true := by decide +kernel
private theorem c1153280 : checkChunk 1153280 128 = true := by decide +kernel
private theorem c1153408 : checkChunk 1153408 128 = true := by decide +kernel
private theorem c1153536 : checkChunk 1153536 128 = true := by decide +kernel
private theorem c1153664 : checkChunk 1153664 128 = true := by decide +kernel
private theorem c1153792 : checkChunk 1153792 128 = true := by decide +kernel
private theorem c1153920 : checkChunk 1153920 128 = true := by decide +kernel
private theorem c1154048 : checkChunk 1154048 128 = true := by decide +kernel
private theorem c1154176 : checkChunk 1154176 128 = true := by decide +kernel
private theorem c1154304 : checkChunk 1154304 128 = true := by decide +kernel
private theorem c1154432 : checkChunk 1154432 128 = true := by decide +kernel
private theorem c1154560 : checkChunk 1154560 128 = true := by decide +kernel
private theorem c1154688 : checkChunk 1154688 128 = true := by decide +kernel
private theorem c1154816 : checkChunk 1154816 128 = true := by decide +kernel
private theorem c1154944 : checkChunk 1154944 128 = true := by decide +kernel

public theorem checked : Checked 1146880 1155072 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1146880 128 c1146880) (checkChunk_sound 1147008 128 c1147008)) (Checked.append (checkChunk_sound 1147136 128 c1147136) (checkChunk_sound 1147264 128 c1147264))) (Checked.append (Checked.append (checkChunk_sound 1147392 128 c1147392) (checkChunk_sound 1147520 128 c1147520)) (Checked.append (checkChunk_sound 1147648 128 c1147648) (checkChunk_sound 1147776 128 c1147776)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1147904 128 c1147904) (checkChunk_sound 1148032 128 c1148032)) (Checked.append (checkChunk_sound 1148160 128 c1148160) (checkChunk_sound 1148288 128 c1148288))) (Checked.append (Checked.append (checkChunk_sound 1148416 128 c1148416) (checkChunk_sound 1148544 128 c1148544)) (Checked.append (checkChunk_sound 1148672 128 c1148672) (checkChunk_sound 1148800 128 c1148800))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1148928 128 c1148928) (checkChunk_sound 1149056 128 c1149056)) (Checked.append (checkChunk_sound 1149184 128 c1149184) (checkChunk_sound 1149312 128 c1149312))) (Checked.append (Checked.append (checkChunk_sound 1149440 128 c1149440) (checkChunk_sound 1149568 128 c1149568)) (Checked.append (checkChunk_sound 1149696 128 c1149696) (checkChunk_sound 1149824 128 c1149824)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1149952 128 c1149952) (checkChunk_sound 1150080 128 c1150080)) (Checked.append (checkChunk_sound 1150208 128 c1150208) (checkChunk_sound 1150336 128 c1150336))) (Checked.append (Checked.append (checkChunk_sound 1150464 128 c1150464) (checkChunk_sound 1150592 128 c1150592)) (Checked.append (checkChunk_sound 1150720 128 c1150720) (checkChunk_sound 1150848 128 c1150848)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1150976 128 c1150976) (checkChunk_sound 1151104 128 c1151104)) (Checked.append (checkChunk_sound 1151232 128 c1151232) (checkChunk_sound 1151360 128 c1151360))) (Checked.append (Checked.append (checkChunk_sound 1151488 128 c1151488) (checkChunk_sound 1151616 128 c1151616)) (Checked.append (checkChunk_sound 1151744 128 c1151744) (checkChunk_sound 1151872 128 c1151872)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1152000 128 c1152000) (checkChunk_sound 1152128 128 c1152128)) (Checked.append (checkChunk_sound 1152256 128 c1152256) (checkChunk_sound 1152384 128 c1152384))) (Checked.append (Checked.append (checkChunk_sound 1152512 128 c1152512) (checkChunk_sound 1152640 128 c1152640)) (Checked.append (checkChunk_sound 1152768 128 c1152768) (checkChunk_sound 1152896 128 c1152896))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1153024 128 c1153024) (checkChunk_sound 1153152 128 c1153152)) (Checked.append (checkChunk_sound 1153280 128 c1153280) (checkChunk_sound 1153408 128 c1153408))) (Checked.append (Checked.append (checkChunk_sound 1153536 128 c1153536) (checkChunk_sound 1153664 128 c1153664)) (Checked.append (checkChunk_sound 1153792 128 c1153792) (checkChunk_sound 1153920 128 c1153920)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1154048 128 c1154048) (checkChunk_sound 1154176 128 c1154176)) (Checked.append (checkChunk_sound 1154304 128 c1154304) (checkChunk_sound 1154432 128 c1154432))) (Checked.append (Checked.append (checkChunk_sound 1154560 128 c1154560) (checkChunk_sound 1154688 128 c1154688)) (Checked.append (checkChunk_sound 1154816 128 c1154816) (checkChunk_sound 1154944 128 c1154944)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B009
