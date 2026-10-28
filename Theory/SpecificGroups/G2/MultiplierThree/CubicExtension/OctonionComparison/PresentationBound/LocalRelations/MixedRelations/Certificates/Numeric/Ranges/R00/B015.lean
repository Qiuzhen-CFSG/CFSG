module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [131072, 139264).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B015
private theorem c131072 : checkChunk 131072 128 = true := by decide +kernel
private theorem c131200 : checkChunk 131200 128 = true := by decide +kernel
private theorem c131328 : checkChunk 131328 128 = true := by decide +kernel
private theorem c131456 : checkChunk 131456 128 = true := by decide +kernel
private theorem c131584 : checkChunk 131584 128 = true := by decide +kernel
private theorem c131712 : checkChunk 131712 128 = true := by decide +kernel
private theorem c131840 : checkChunk 131840 128 = true := by decide +kernel
private theorem c131968 : checkChunk 131968 128 = true := by decide +kernel
private theorem c132096 : checkChunk 132096 128 = true := by decide +kernel
private theorem c132224 : checkChunk 132224 128 = true := by decide +kernel
private theorem c132352 : checkChunk 132352 128 = true := by decide +kernel
private theorem c132480 : checkChunk 132480 128 = true := by decide +kernel
private theorem c132608 : checkChunk 132608 128 = true := by decide +kernel
private theorem c132736 : checkChunk 132736 128 = true := by decide +kernel
private theorem c132864 : checkChunk 132864 128 = true := by decide +kernel
private theorem c132992 : checkChunk 132992 128 = true := by decide +kernel
private theorem c133120 : checkChunk 133120 128 = true := by decide +kernel
private theorem c133248 : checkChunk 133248 128 = true := by decide +kernel
private theorem c133376 : checkChunk 133376 128 = true := by decide +kernel
private theorem c133504 : checkChunk 133504 128 = true := by decide +kernel
private theorem c133632 : checkChunk 133632 128 = true := by decide +kernel
private theorem c133760 : checkChunk 133760 128 = true := by decide +kernel
private theorem c133888 : checkChunk 133888 128 = true := by decide +kernel
private theorem c134016 : checkChunk 134016 128 = true := by decide +kernel
private theorem c134144 : checkChunk 134144 128 = true := by decide +kernel
private theorem c134272 : checkChunk 134272 128 = true := by decide +kernel
private theorem c134400 : checkChunk 134400 128 = true := by decide +kernel
private theorem c134528 : checkChunk 134528 128 = true := by decide +kernel
private theorem c134656 : checkChunk 134656 128 = true := by decide +kernel
private theorem c134784 : checkChunk 134784 128 = true := by decide +kernel
private theorem c134912 : checkChunk 134912 128 = true := by decide +kernel
private theorem c135040 : checkChunk 135040 128 = true := by decide +kernel
private theorem c135168 : checkChunk 135168 128 = true := by decide +kernel
private theorem c135296 : checkChunk 135296 128 = true := by decide +kernel
private theorem c135424 : checkChunk 135424 128 = true := by decide +kernel
private theorem c135552 : checkChunk 135552 128 = true := by decide +kernel
private theorem c135680 : checkChunk 135680 128 = true := by decide +kernel
private theorem c135808 : checkChunk 135808 128 = true := by decide +kernel
private theorem c135936 : checkChunk 135936 128 = true := by decide +kernel
private theorem c136064 : checkChunk 136064 128 = true := by decide +kernel
private theorem c136192 : checkChunk 136192 128 = true := by decide +kernel
private theorem c136320 : checkChunk 136320 128 = true := by decide +kernel
private theorem c136448 : checkChunk 136448 128 = true := by decide +kernel
private theorem c136576 : checkChunk 136576 128 = true := by decide +kernel
private theorem c136704 : checkChunk 136704 128 = true := by decide +kernel
private theorem c136832 : checkChunk 136832 128 = true := by decide +kernel
private theorem c136960 : checkChunk 136960 128 = true := by decide +kernel
private theorem c137088 : checkChunk 137088 128 = true := by decide +kernel
private theorem c137216 : checkChunk 137216 128 = true := by decide +kernel
private theorem c137344 : checkChunk 137344 128 = true := by decide +kernel
private theorem c137472 : checkChunk 137472 128 = true := by decide +kernel
private theorem c137600 : checkChunk 137600 128 = true := by decide +kernel
private theorem c137728 : checkChunk 137728 128 = true := by decide +kernel
private theorem c137856 : checkChunk 137856 128 = true := by decide +kernel
private theorem c137984 : checkChunk 137984 128 = true := by decide +kernel
private theorem c138112 : checkChunk 138112 128 = true := by decide +kernel
private theorem c138240 : checkChunk 138240 128 = true := by decide +kernel
private theorem c138368 : checkChunk 138368 128 = true := by decide +kernel
private theorem c138496 : checkChunk 138496 128 = true := by decide +kernel
private theorem c138624 : checkChunk 138624 128 = true := by decide +kernel
private theorem c138752 : checkChunk 138752 128 = true := by decide +kernel
private theorem c138880 : checkChunk 138880 128 = true := by decide +kernel
private theorem c139008 : checkChunk 139008 128 = true := by decide +kernel
private theorem c139136 : checkChunk 139136 128 = true := by decide +kernel

public theorem checked : Checked 131072 139264 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 131072 128 c131072) (checkChunk_sound 131200 128 c131200)) (Checked.append (checkChunk_sound 131328 128 c131328) (checkChunk_sound 131456 128 c131456))) (Checked.append (Checked.append (checkChunk_sound 131584 128 c131584) (checkChunk_sound 131712 128 c131712)) (Checked.append (checkChunk_sound 131840 128 c131840) (checkChunk_sound 131968 128 c131968)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 132096 128 c132096) (checkChunk_sound 132224 128 c132224)) (Checked.append (checkChunk_sound 132352 128 c132352) (checkChunk_sound 132480 128 c132480))) (Checked.append (Checked.append (checkChunk_sound 132608 128 c132608) (checkChunk_sound 132736 128 c132736)) (Checked.append (checkChunk_sound 132864 128 c132864) (checkChunk_sound 132992 128 c132992))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 133120 128 c133120) (checkChunk_sound 133248 128 c133248)) (Checked.append (checkChunk_sound 133376 128 c133376) (checkChunk_sound 133504 128 c133504))) (Checked.append (Checked.append (checkChunk_sound 133632 128 c133632) (checkChunk_sound 133760 128 c133760)) (Checked.append (checkChunk_sound 133888 128 c133888) (checkChunk_sound 134016 128 c134016)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 134144 128 c134144) (checkChunk_sound 134272 128 c134272)) (Checked.append (checkChunk_sound 134400 128 c134400) (checkChunk_sound 134528 128 c134528))) (Checked.append (Checked.append (checkChunk_sound 134656 128 c134656) (checkChunk_sound 134784 128 c134784)) (Checked.append (checkChunk_sound 134912 128 c134912) (checkChunk_sound 135040 128 c135040)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 135168 128 c135168) (checkChunk_sound 135296 128 c135296)) (Checked.append (checkChunk_sound 135424 128 c135424) (checkChunk_sound 135552 128 c135552))) (Checked.append (Checked.append (checkChunk_sound 135680 128 c135680) (checkChunk_sound 135808 128 c135808)) (Checked.append (checkChunk_sound 135936 128 c135936) (checkChunk_sound 136064 128 c136064)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 136192 128 c136192) (checkChunk_sound 136320 128 c136320)) (Checked.append (checkChunk_sound 136448 128 c136448) (checkChunk_sound 136576 128 c136576))) (Checked.append (Checked.append (checkChunk_sound 136704 128 c136704) (checkChunk_sound 136832 128 c136832)) (Checked.append (checkChunk_sound 136960 128 c136960) (checkChunk_sound 137088 128 c137088))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 137216 128 c137216) (checkChunk_sound 137344 128 c137344)) (Checked.append (checkChunk_sound 137472 128 c137472) (checkChunk_sound 137600 128 c137600))) (Checked.append (Checked.append (checkChunk_sound 137728 128 c137728) (checkChunk_sound 137856 128 c137856)) (Checked.append (checkChunk_sound 137984 128 c137984) (checkChunk_sound 138112 128 c138112)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 138240 128 c138240) (checkChunk_sound 138368 128 c138368)) (Checked.append (checkChunk_sound 138496 128 c138496) (checkChunk_sound 138624 128 c138624))) (Checked.append (Checked.append (checkChunk_sound 138752 128 c138752) (checkChunk_sound 138880 128 c138880)) (Checked.append (checkChunk_sound 139008 128 c139008) (checkChunk_sound 139136 128 c139136)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B015
