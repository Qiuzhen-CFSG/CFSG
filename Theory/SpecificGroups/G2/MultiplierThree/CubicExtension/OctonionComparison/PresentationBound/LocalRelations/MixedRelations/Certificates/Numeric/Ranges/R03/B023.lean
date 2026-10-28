module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [835584, 843776).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B023
private theorem c835584 : checkChunk 835584 128 = true := by decide +kernel
private theorem c835712 : checkChunk 835712 128 = true := by decide +kernel
private theorem c835840 : checkChunk 835840 128 = true := by decide +kernel
private theorem c835968 : checkChunk 835968 128 = true := by decide +kernel
private theorem c836096 : checkChunk 836096 128 = true := by decide +kernel
private theorem c836224 : checkChunk 836224 128 = true := by decide +kernel
private theorem c836352 : checkChunk 836352 128 = true := by decide +kernel
private theorem c836480 : checkChunk 836480 128 = true := by decide +kernel
private theorem c836608 : checkChunk 836608 128 = true := by decide +kernel
private theorem c836736 : checkChunk 836736 128 = true := by decide +kernel
private theorem c836864 : checkChunk 836864 128 = true := by decide +kernel
private theorem c836992 : checkChunk 836992 128 = true := by decide +kernel
private theorem c837120 : checkChunk 837120 128 = true := by decide +kernel
private theorem c837248 : checkChunk 837248 128 = true := by decide +kernel
private theorem c837376 : checkChunk 837376 128 = true := by decide +kernel
private theorem c837504 : checkChunk 837504 128 = true := by decide +kernel
private theorem c837632 : checkChunk 837632 128 = true := by decide +kernel
private theorem c837760 : checkChunk 837760 128 = true := by decide +kernel
private theorem c837888 : checkChunk 837888 128 = true := by decide +kernel
private theorem c838016 : checkChunk 838016 128 = true := by decide +kernel
private theorem c838144 : checkChunk 838144 128 = true := by decide +kernel
private theorem c838272 : checkChunk 838272 128 = true := by decide +kernel
private theorem c838400 : checkChunk 838400 128 = true := by decide +kernel
private theorem c838528 : checkChunk 838528 128 = true := by decide +kernel
private theorem c838656 : checkChunk 838656 128 = true := by decide +kernel
private theorem c838784 : checkChunk 838784 128 = true := by decide +kernel
private theorem c838912 : checkChunk 838912 128 = true := by decide +kernel
private theorem c839040 : checkChunk 839040 128 = true := by decide +kernel
private theorem c839168 : checkChunk 839168 128 = true := by decide +kernel
private theorem c839296 : checkChunk 839296 128 = true := by decide +kernel
private theorem c839424 : checkChunk 839424 128 = true := by decide +kernel
private theorem c839552 : checkChunk 839552 128 = true := by decide +kernel
private theorem c839680 : checkChunk 839680 128 = true := by decide +kernel
private theorem c839808 : checkChunk 839808 128 = true := by decide +kernel
private theorem c839936 : checkChunk 839936 128 = true := by decide +kernel
private theorem c840064 : checkChunk 840064 128 = true := by decide +kernel
private theorem c840192 : checkChunk 840192 128 = true := by decide +kernel
private theorem c840320 : checkChunk 840320 128 = true := by decide +kernel
private theorem c840448 : checkChunk 840448 128 = true := by decide +kernel
private theorem c840576 : checkChunk 840576 128 = true := by decide +kernel
private theorem c840704 : checkChunk 840704 128 = true := by decide +kernel
private theorem c840832 : checkChunk 840832 128 = true := by decide +kernel
private theorem c840960 : checkChunk 840960 128 = true := by decide +kernel
private theorem c841088 : checkChunk 841088 128 = true := by decide +kernel
private theorem c841216 : checkChunk 841216 128 = true := by decide +kernel
private theorem c841344 : checkChunk 841344 128 = true := by decide +kernel
private theorem c841472 : checkChunk 841472 128 = true := by decide +kernel
private theorem c841600 : checkChunk 841600 128 = true := by decide +kernel
private theorem c841728 : checkChunk 841728 128 = true := by decide +kernel
private theorem c841856 : checkChunk 841856 128 = true := by decide +kernel
private theorem c841984 : checkChunk 841984 128 = true := by decide +kernel
private theorem c842112 : checkChunk 842112 128 = true := by decide +kernel
private theorem c842240 : checkChunk 842240 128 = true := by decide +kernel
private theorem c842368 : checkChunk 842368 128 = true := by decide +kernel
private theorem c842496 : checkChunk 842496 128 = true := by decide +kernel
private theorem c842624 : checkChunk 842624 128 = true := by decide +kernel
private theorem c842752 : checkChunk 842752 128 = true := by decide +kernel
private theorem c842880 : checkChunk 842880 128 = true := by decide +kernel
private theorem c843008 : checkChunk 843008 128 = true := by decide +kernel
private theorem c843136 : checkChunk 843136 128 = true := by decide +kernel
private theorem c843264 : checkChunk 843264 128 = true := by decide +kernel
private theorem c843392 : checkChunk 843392 128 = true := by decide +kernel
private theorem c843520 : checkChunk 843520 128 = true := by decide +kernel
private theorem c843648 : checkChunk 843648 128 = true := by decide +kernel

public theorem checked : Checked 835584 843776 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 835584 128 c835584) (checkChunk_sound 835712 128 c835712)) (Checked.append (checkChunk_sound 835840 128 c835840) (checkChunk_sound 835968 128 c835968))) (Checked.append (Checked.append (checkChunk_sound 836096 128 c836096) (checkChunk_sound 836224 128 c836224)) (Checked.append (checkChunk_sound 836352 128 c836352) (checkChunk_sound 836480 128 c836480)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 836608 128 c836608) (checkChunk_sound 836736 128 c836736)) (Checked.append (checkChunk_sound 836864 128 c836864) (checkChunk_sound 836992 128 c836992))) (Checked.append (Checked.append (checkChunk_sound 837120 128 c837120) (checkChunk_sound 837248 128 c837248)) (Checked.append (checkChunk_sound 837376 128 c837376) (checkChunk_sound 837504 128 c837504))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 837632 128 c837632) (checkChunk_sound 837760 128 c837760)) (Checked.append (checkChunk_sound 837888 128 c837888) (checkChunk_sound 838016 128 c838016))) (Checked.append (Checked.append (checkChunk_sound 838144 128 c838144) (checkChunk_sound 838272 128 c838272)) (Checked.append (checkChunk_sound 838400 128 c838400) (checkChunk_sound 838528 128 c838528)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 838656 128 c838656) (checkChunk_sound 838784 128 c838784)) (Checked.append (checkChunk_sound 838912 128 c838912) (checkChunk_sound 839040 128 c839040))) (Checked.append (Checked.append (checkChunk_sound 839168 128 c839168) (checkChunk_sound 839296 128 c839296)) (Checked.append (checkChunk_sound 839424 128 c839424) (checkChunk_sound 839552 128 c839552)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 839680 128 c839680) (checkChunk_sound 839808 128 c839808)) (Checked.append (checkChunk_sound 839936 128 c839936) (checkChunk_sound 840064 128 c840064))) (Checked.append (Checked.append (checkChunk_sound 840192 128 c840192) (checkChunk_sound 840320 128 c840320)) (Checked.append (checkChunk_sound 840448 128 c840448) (checkChunk_sound 840576 128 c840576)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 840704 128 c840704) (checkChunk_sound 840832 128 c840832)) (Checked.append (checkChunk_sound 840960 128 c840960) (checkChunk_sound 841088 128 c841088))) (Checked.append (Checked.append (checkChunk_sound 841216 128 c841216) (checkChunk_sound 841344 128 c841344)) (Checked.append (checkChunk_sound 841472 128 c841472) (checkChunk_sound 841600 128 c841600))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 841728 128 c841728) (checkChunk_sound 841856 128 c841856)) (Checked.append (checkChunk_sound 841984 128 c841984) (checkChunk_sound 842112 128 c842112))) (Checked.append (Checked.append (checkChunk_sound 842240 128 c842240) (checkChunk_sound 842368 128 c842368)) (Checked.append (checkChunk_sound 842496 128 c842496) (checkChunk_sound 842624 128 c842624)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 842752 128 c842752) (checkChunk_sound 842880 128 c842880)) (Checked.append (checkChunk_sound 843008 128 c843008) (checkChunk_sound 843136 128 c843136))) (Checked.append (Checked.append (checkChunk_sound 843264 128 c843264) (checkChunk_sound 843392 128 c843392)) (Checked.append (checkChunk_sound 843520 128 c843520) (checkChunk_sound 843648 128 c843648)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B023
