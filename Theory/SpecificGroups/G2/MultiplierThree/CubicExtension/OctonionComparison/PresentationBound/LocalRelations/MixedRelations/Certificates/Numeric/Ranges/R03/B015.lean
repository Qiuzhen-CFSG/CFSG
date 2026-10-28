module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [770048, 778240).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B015
private theorem c770048 : checkChunk 770048 128 = true := by decide +kernel
private theorem c770176 : checkChunk 770176 128 = true := by decide +kernel
private theorem c770304 : checkChunk 770304 128 = true := by decide +kernel
private theorem c770432 : checkChunk 770432 128 = true := by decide +kernel
private theorem c770560 : checkChunk 770560 128 = true := by decide +kernel
private theorem c770688 : checkChunk 770688 128 = true := by decide +kernel
private theorem c770816 : checkChunk 770816 128 = true := by decide +kernel
private theorem c770944 : checkChunk 770944 128 = true := by decide +kernel
private theorem c771072 : checkChunk 771072 128 = true := by decide +kernel
private theorem c771200 : checkChunk 771200 128 = true := by decide +kernel
private theorem c771328 : checkChunk 771328 128 = true := by decide +kernel
private theorem c771456 : checkChunk 771456 128 = true := by decide +kernel
private theorem c771584 : checkChunk 771584 128 = true := by decide +kernel
private theorem c771712 : checkChunk 771712 128 = true := by decide +kernel
private theorem c771840 : checkChunk 771840 128 = true := by decide +kernel
private theorem c771968 : checkChunk 771968 128 = true := by decide +kernel
private theorem c772096 : checkChunk 772096 128 = true := by decide +kernel
private theorem c772224 : checkChunk 772224 128 = true := by decide +kernel
private theorem c772352 : checkChunk 772352 128 = true := by decide +kernel
private theorem c772480 : checkChunk 772480 128 = true := by decide +kernel
private theorem c772608 : checkChunk 772608 128 = true := by decide +kernel
private theorem c772736 : checkChunk 772736 128 = true := by decide +kernel
private theorem c772864 : checkChunk 772864 128 = true := by decide +kernel
private theorem c772992 : checkChunk 772992 128 = true := by decide +kernel
private theorem c773120 : checkChunk 773120 128 = true := by decide +kernel
private theorem c773248 : checkChunk 773248 128 = true := by decide +kernel
private theorem c773376 : checkChunk 773376 128 = true := by decide +kernel
private theorem c773504 : checkChunk 773504 128 = true := by decide +kernel
private theorem c773632 : checkChunk 773632 128 = true := by decide +kernel
private theorem c773760 : checkChunk 773760 128 = true := by decide +kernel
private theorem c773888 : checkChunk 773888 128 = true := by decide +kernel
private theorem c774016 : checkChunk 774016 128 = true := by decide +kernel
private theorem c774144 : checkChunk 774144 128 = true := by decide +kernel
private theorem c774272 : checkChunk 774272 128 = true := by decide +kernel
private theorem c774400 : checkChunk 774400 128 = true := by decide +kernel
private theorem c774528 : checkChunk 774528 128 = true := by decide +kernel
private theorem c774656 : checkChunk 774656 128 = true := by decide +kernel
private theorem c774784 : checkChunk 774784 128 = true := by decide +kernel
private theorem c774912 : checkChunk 774912 128 = true := by decide +kernel
private theorem c775040 : checkChunk 775040 128 = true := by decide +kernel
private theorem c775168 : checkChunk 775168 128 = true := by decide +kernel
private theorem c775296 : checkChunk 775296 128 = true := by decide +kernel
private theorem c775424 : checkChunk 775424 128 = true := by decide +kernel
private theorem c775552 : checkChunk 775552 128 = true := by decide +kernel
private theorem c775680 : checkChunk 775680 128 = true := by decide +kernel
private theorem c775808 : checkChunk 775808 128 = true := by decide +kernel
private theorem c775936 : checkChunk 775936 128 = true := by decide +kernel
private theorem c776064 : checkChunk 776064 128 = true := by decide +kernel
private theorem c776192 : checkChunk 776192 128 = true := by decide +kernel
private theorem c776320 : checkChunk 776320 128 = true := by decide +kernel
private theorem c776448 : checkChunk 776448 128 = true := by decide +kernel
private theorem c776576 : checkChunk 776576 128 = true := by decide +kernel
private theorem c776704 : checkChunk 776704 128 = true := by decide +kernel
private theorem c776832 : checkChunk 776832 128 = true := by decide +kernel
private theorem c776960 : checkChunk 776960 128 = true := by decide +kernel
private theorem c777088 : checkChunk 777088 128 = true := by decide +kernel
private theorem c777216 : checkChunk 777216 128 = true := by decide +kernel
private theorem c777344 : checkChunk 777344 128 = true := by decide +kernel
private theorem c777472 : checkChunk 777472 128 = true := by decide +kernel
private theorem c777600 : checkChunk 777600 128 = true := by decide +kernel
private theorem c777728 : checkChunk 777728 128 = true := by decide +kernel
private theorem c777856 : checkChunk 777856 128 = true := by decide +kernel
private theorem c777984 : checkChunk 777984 128 = true := by decide +kernel
private theorem c778112 : checkChunk 778112 128 = true := by decide +kernel

public theorem checked : Checked 770048 778240 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 770048 128 c770048) (checkChunk_sound 770176 128 c770176)) (Checked.append (checkChunk_sound 770304 128 c770304) (checkChunk_sound 770432 128 c770432))) (Checked.append (Checked.append (checkChunk_sound 770560 128 c770560) (checkChunk_sound 770688 128 c770688)) (Checked.append (checkChunk_sound 770816 128 c770816) (checkChunk_sound 770944 128 c770944)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 771072 128 c771072) (checkChunk_sound 771200 128 c771200)) (Checked.append (checkChunk_sound 771328 128 c771328) (checkChunk_sound 771456 128 c771456))) (Checked.append (Checked.append (checkChunk_sound 771584 128 c771584) (checkChunk_sound 771712 128 c771712)) (Checked.append (checkChunk_sound 771840 128 c771840) (checkChunk_sound 771968 128 c771968))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 772096 128 c772096) (checkChunk_sound 772224 128 c772224)) (Checked.append (checkChunk_sound 772352 128 c772352) (checkChunk_sound 772480 128 c772480))) (Checked.append (Checked.append (checkChunk_sound 772608 128 c772608) (checkChunk_sound 772736 128 c772736)) (Checked.append (checkChunk_sound 772864 128 c772864) (checkChunk_sound 772992 128 c772992)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 773120 128 c773120) (checkChunk_sound 773248 128 c773248)) (Checked.append (checkChunk_sound 773376 128 c773376) (checkChunk_sound 773504 128 c773504))) (Checked.append (Checked.append (checkChunk_sound 773632 128 c773632) (checkChunk_sound 773760 128 c773760)) (Checked.append (checkChunk_sound 773888 128 c773888) (checkChunk_sound 774016 128 c774016)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 774144 128 c774144) (checkChunk_sound 774272 128 c774272)) (Checked.append (checkChunk_sound 774400 128 c774400) (checkChunk_sound 774528 128 c774528))) (Checked.append (Checked.append (checkChunk_sound 774656 128 c774656) (checkChunk_sound 774784 128 c774784)) (Checked.append (checkChunk_sound 774912 128 c774912) (checkChunk_sound 775040 128 c775040)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 775168 128 c775168) (checkChunk_sound 775296 128 c775296)) (Checked.append (checkChunk_sound 775424 128 c775424) (checkChunk_sound 775552 128 c775552))) (Checked.append (Checked.append (checkChunk_sound 775680 128 c775680) (checkChunk_sound 775808 128 c775808)) (Checked.append (checkChunk_sound 775936 128 c775936) (checkChunk_sound 776064 128 c776064))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 776192 128 c776192) (checkChunk_sound 776320 128 c776320)) (Checked.append (checkChunk_sound 776448 128 c776448) (checkChunk_sound 776576 128 c776576))) (Checked.append (Checked.append (checkChunk_sound 776704 128 c776704) (checkChunk_sound 776832 128 c776832)) (Checked.append (checkChunk_sound 776960 128 c776960) (checkChunk_sound 777088 128 c777088)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 777216 128 c777216) (checkChunk_sound 777344 128 c777344)) (Checked.append (checkChunk_sound 777472 128 c777472) (checkChunk_sound 777600 128 c777600))) (Checked.append (Checked.append (checkChunk_sound 777728 128 c777728) (checkChunk_sound 777856 128 c777856)) (Checked.append (checkChunk_sound 777984 128 c777984) (checkChunk_sound 778112 128 c778112)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B015
