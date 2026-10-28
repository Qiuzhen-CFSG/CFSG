module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [540672, 548864).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B013
private theorem c540672 : checkChunk 540672 128 = true := by decide +kernel
private theorem c540800 : checkChunk 540800 128 = true := by decide +kernel
private theorem c540928 : checkChunk 540928 128 = true := by decide +kernel
private theorem c541056 : checkChunk 541056 128 = true := by decide +kernel
private theorem c541184 : checkChunk 541184 128 = true := by decide +kernel
private theorem c541312 : checkChunk 541312 128 = true := by decide +kernel
private theorem c541440 : checkChunk 541440 128 = true := by decide +kernel
private theorem c541568 : checkChunk 541568 128 = true := by decide +kernel
private theorem c541696 : checkChunk 541696 128 = true := by decide +kernel
private theorem c541824 : checkChunk 541824 128 = true := by decide +kernel
private theorem c541952 : checkChunk 541952 128 = true := by decide +kernel
private theorem c542080 : checkChunk 542080 128 = true := by decide +kernel
private theorem c542208 : checkChunk 542208 128 = true := by decide +kernel
private theorem c542336 : checkChunk 542336 128 = true := by decide +kernel
private theorem c542464 : checkChunk 542464 128 = true := by decide +kernel
private theorem c542592 : checkChunk 542592 128 = true := by decide +kernel
private theorem c542720 : checkChunk 542720 128 = true := by decide +kernel
private theorem c542848 : checkChunk 542848 128 = true := by decide +kernel
private theorem c542976 : checkChunk 542976 128 = true := by decide +kernel
private theorem c543104 : checkChunk 543104 128 = true := by decide +kernel
private theorem c543232 : checkChunk 543232 128 = true := by decide +kernel
private theorem c543360 : checkChunk 543360 128 = true := by decide +kernel
private theorem c543488 : checkChunk 543488 128 = true := by decide +kernel
private theorem c543616 : checkChunk 543616 128 = true := by decide +kernel
private theorem c543744 : checkChunk 543744 128 = true := by decide +kernel
private theorem c543872 : checkChunk 543872 128 = true := by decide +kernel
private theorem c544000 : checkChunk 544000 128 = true := by decide +kernel
private theorem c544128 : checkChunk 544128 128 = true := by decide +kernel
private theorem c544256 : checkChunk 544256 128 = true := by decide +kernel
private theorem c544384 : checkChunk 544384 128 = true := by decide +kernel
private theorem c544512 : checkChunk 544512 128 = true := by decide +kernel
private theorem c544640 : checkChunk 544640 128 = true := by decide +kernel
private theorem c544768 : checkChunk 544768 128 = true := by decide +kernel
private theorem c544896 : checkChunk 544896 128 = true := by decide +kernel
private theorem c545024 : checkChunk 545024 128 = true := by decide +kernel
private theorem c545152 : checkChunk 545152 128 = true := by decide +kernel
private theorem c545280 : checkChunk 545280 128 = true := by decide +kernel
private theorem c545408 : checkChunk 545408 128 = true := by decide +kernel
private theorem c545536 : checkChunk 545536 128 = true := by decide +kernel
private theorem c545664 : checkChunk 545664 128 = true := by decide +kernel
private theorem c545792 : checkChunk 545792 128 = true := by decide +kernel
private theorem c545920 : checkChunk 545920 128 = true := by decide +kernel
private theorem c546048 : checkChunk 546048 128 = true := by decide +kernel
private theorem c546176 : checkChunk 546176 128 = true := by decide +kernel
private theorem c546304 : checkChunk 546304 128 = true := by decide +kernel
private theorem c546432 : checkChunk 546432 128 = true := by decide +kernel
private theorem c546560 : checkChunk 546560 128 = true := by decide +kernel
private theorem c546688 : checkChunk 546688 128 = true := by decide +kernel
private theorem c546816 : checkChunk 546816 128 = true := by decide +kernel
private theorem c546944 : checkChunk 546944 128 = true := by decide +kernel
private theorem c547072 : checkChunk 547072 128 = true := by decide +kernel
private theorem c547200 : checkChunk 547200 128 = true := by decide +kernel
private theorem c547328 : checkChunk 547328 128 = true := by decide +kernel
private theorem c547456 : checkChunk 547456 128 = true := by decide +kernel
private theorem c547584 : checkChunk 547584 128 = true := by decide +kernel
private theorem c547712 : checkChunk 547712 128 = true := by decide +kernel
private theorem c547840 : checkChunk 547840 128 = true := by decide +kernel
private theorem c547968 : checkChunk 547968 128 = true := by decide +kernel
private theorem c548096 : checkChunk 548096 128 = true := by decide +kernel
private theorem c548224 : checkChunk 548224 128 = true := by decide +kernel
private theorem c548352 : checkChunk 548352 128 = true := by decide +kernel
private theorem c548480 : checkChunk 548480 128 = true := by decide +kernel
private theorem c548608 : checkChunk 548608 128 = true := by decide +kernel
private theorem c548736 : checkChunk 548736 128 = true := by decide +kernel

public theorem checked : Checked 540672 548864 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 540672 128 c540672) (checkChunk_sound 540800 128 c540800)) (Checked.append (checkChunk_sound 540928 128 c540928) (checkChunk_sound 541056 128 c541056))) (Checked.append (Checked.append (checkChunk_sound 541184 128 c541184) (checkChunk_sound 541312 128 c541312)) (Checked.append (checkChunk_sound 541440 128 c541440) (checkChunk_sound 541568 128 c541568)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 541696 128 c541696) (checkChunk_sound 541824 128 c541824)) (Checked.append (checkChunk_sound 541952 128 c541952) (checkChunk_sound 542080 128 c542080))) (Checked.append (Checked.append (checkChunk_sound 542208 128 c542208) (checkChunk_sound 542336 128 c542336)) (Checked.append (checkChunk_sound 542464 128 c542464) (checkChunk_sound 542592 128 c542592))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 542720 128 c542720) (checkChunk_sound 542848 128 c542848)) (Checked.append (checkChunk_sound 542976 128 c542976) (checkChunk_sound 543104 128 c543104))) (Checked.append (Checked.append (checkChunk_sound 543232 128 c543232) (checkChunk_sound 543360 128 c543360)) (Checked.append (checkChunk_sound 543488 128 c543488) (checkChunk_sound 543616 128 c543616)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 543744 128 c543744) (checkChunk_sound 543872 128 c543872)) (Checked.append (checkChunk_sound 544000 128 c544000) (checkChunk_sound 544128 128 c544128))) (Checked.append (Checked.append (checkChunk_sound 544256 128 c544256) (checkChunk_sound 544384 128 c544384)) (Checked.append (checkChunk_sound 544512 128 c544512) (checkChunk_sound 544640 128 c544640)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 544768 128 c544768) (checkChunk_sound 544896 128 c544896)) (Checked.append (checkChunk_sound 545024 128 c545024) (checkChunk_sound 545152 128 c545152))) (Checked.append (Checked.append (checkChunk_sound 545280 128 c545280) (checkChunk_sound 545408 128 c545408)) (Checked.append (checkChunk_sound 545536 128 c545536) (checkChunk_sound 545664 128 c545664)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 545792 128 c545792) (checkChunk_sound 545920 128 c545920)) (Checked.append (checkChunk_sound 546048 128 c546048) (checkChunk_sound 546176 128 c546176))) (Checked.append (Checked.append (checkChunk_sound 546304 128 c546304) (checkChunk_sound 546432 128 c546432)) (Checked.append (checkChunk_sound 546560 128 c546560) (checkChunk_sound 546688 128 c546688))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 546816 128 c546816) (checkChunk_sound 546944 128 c546944)) (Checked.append (checkChunk_sound 547072 128 c547072) (checkChunk_sound 547200 128 c547200))) (Checked.append (Checked.append (checkChunk_sound 547328 128 c547328) (checkChunk_sound 547456 128 c547456)) (Checked.append (checkChunk_sound 547584 128 c547584) (checkChunk_sound 547712 128 c547712)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 547840 128 c547840) (checkChunk_sound 547968 128 c547968)) (Checked.append (checkChunk_sound 548096 128 c548096) (checkChunk_sound 548224 128 c548224))) (Checked.append (Checked.append (checkChunk_sound 548352 128 c548352) (checkChunk_sound 548480 128 c548480)) (Checked.append (checkChunk_sound 548608 128 c548608) (checkChunk_sound 548736 128 c548736)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B013
