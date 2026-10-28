module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [737280, 745472).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B011
private theorem c737280 : checkChunk 737280 128 = true := by decide +kernel
private theorem c737408 : checkChunk 737408 128 = true := by decide +kernel
private theorem c737536 : checkChunk 737536 128 = true := by decide +kernel
private theorem c737664 : checkChunk 737664 128 = true := by decide +kernel
private theorem c737792 : checkChunk 737792 128 = true := by decide +kernel
private theorem c737920 : checkChunk 737920 128 = true := by decide +kernel
private theorem c738048 : checkChunk 738048 128 = true := by decide +kernel
private theorem c738176 : checkChunk 738176 128 = true := by decide +kernel
private theorem c738304 : checkChunk 738304 128 = true := by decide +kernel
private theorem c738432 : checkChunk 738432 128 = true := by decide +kernel
private theorem c738560 : checkChunk 738560 128 = true := by decide +kernel
private theorem c738688 : checkChunk 738688 128 = true := by decide +kernel
private theorem c738816 : checkChunk 738816 128 = true := by decide +kernel
private theorem c738944 : checkChunk 738944 128 = true := by decide +kernel
private theorem c739072 : checkChunk 739072 128 = true := by decide +kernel
private theorem c739200 : checkChunk 739200 128 = true := by decide +kernel
private theorem c739328 : checkChunk 739328 128 = true := by decide +kernel
private theorem c739456 : checkChunk 739456 128 = true := by decide +kernel
private theorem c739584 : checkChunk 739584 128 = true := by decide +kernel
private theorem c739712 : checkChunk 739712 128 = true := by decide +kernel
private theorem c739840 : checkChunk 739840 128 = true := by decide +kernel
private theorem c739968 : checkChunk 739968 128 = true := by decide +kernel
private theorem c740096 : checkChunk 740096 128 = true := by decide +kernel
private theorem c740224 : checkChunk 740224 128 = true := by decide +kernel
private theorem c740352 : checkChunk 740352 128 = true := by decide +kernel
private theorem c740480 : checkChunk 740480 128 = true := by decide +kernel
private theorem c740608 : checkChunk 740608 128 = true := by decide +kernel
private theorem c740736 : checkChunk 740736 128 = true := by decide +kernel
private theorem c740864 : checkChunk 740864 128 = true := by decide +kernel
private theorem c740992 : checkChunk 740992 128 = true := by decide +kernel
private theorem c741120 : checkChunk 741120 128 = true := by decide +kernel
private theorem c741248 : checkChunk 741248 128 = true := by decide +kernel
private theorem c741376 : checkChunk 741376 128 = true := by decide +kernel
private theorem c741504 : checkChunk 741504 128 = true := by decide +kernel
private theorem c741632 : checkChunk 741632 128 = true := by decide +kernel
private theorem c741760 : checkChunk 741760 128 = true := by decide +kernel
private theorem c741888 : checkChunk 741888 128 = true := by decide +kernel
private theorem c742016 : checkChunk 742016 128 = true := by decide +kernel
private theorem c742144 : checkChunk 742144 128 = true := by decide +kernel
private theorem c742272 : checkChunk 742272 128 = true := by decide +kernel
private theorem c742400 : checkChunk 742400 128 = true := by decide +kernel
private theorem c742528 : checkChunk 742528 128 = true := by decide +kernel
private theorem c742656 : checkChunk 742656 128 = true := by decide +kernel
private theorem c742784 : checkChunk 742784 128 = true := by decide +kernel
private theorem c742912 : checkChunk 742912 128 = true := by decide +kernel
private theorem c743040 : checkChunk 743040 128 = true := by decide +kernel
private theorem c743168 : checkChunk 743168 128 = true := by decide +kernel
private theorem c743296 : checkChunk 743296 128 = true := by decide +kernel
private theorem c743424 : checkChunk 743424 128 = true := by decide +kernel
private theorem c743552 : checkChunk 743552 128 = true := by decide +kernel
private theorem c743680 : checkChunk 743680 128 = true := by decide +kernel
private theorem c743808 : checkChunk 743808 128 = true := by decide +kernel
private theorem c743936 : checkChunk 743936 128 = true := by decide +kernel
private theorem c744064 : checkChunk 744064 128 = true := by decide +kernel
private theorem c744192 : checkChunk 744192 128 = true := by decide +kernel
private theorem c744320 : checkChunk 744320 128 = true := by decide +kernel
private theorem c744448 : checkChunk 744448 128 = true := by decide +kernel
private theorem c744576 : checkChunk 744576 128 = true := by decide +kernel
private theorem c744704 : checkChunk 744704 128 = true := by decide +kernel
private theorem c744832 : checkChunk 744832 128 = true := by decide +kernel
private theorem c744960 : checkChunk 744960 128 = true := by decide +kernel
private theorem c745088 : checkChunk 745088 128 = true := by decide +kernel
private theorem c745216 : checkChunk 745216 128 = true := by decide +kernel
private theorem c745344 : checkChunk 745344 128 = true := by decide +kernel

public theorem checked : Checked 737280 745472 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 737280 128 c737280) (checkChunk_sound 737408 128 c737408)) (Checked.append (checkChunk_sound 737536 128 c737536) (checkChunk_sound 737664 128 c737664))) (Checked.append (Checked.append (checkChunk_sound 737792 128 c737792) (checkChunk_sound 737920 128 c737920)) (Checked.append (checkChunk_sound 738048 128 c738048) (checkChunk_sound 738176 128 c738176)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 738304 128 c738304) (checkChunk_sound 738432 128 c738432)) (Checked.append (checkChunk_sound 738560 128 c738560) (checkChunk_sound 738688 128 c738688))) (Checked.append (Checked.append (checkChunk_sound 738816 128 c738816) (checkChunk_sound 738944 128 c738944)) (Checked.append (checkChunk_sound 739072 128 c739072) (checkChunk_sound 739200 128 c739200))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 739328 128 c739328) (checkChunk_sound 739456 128 c739456)) (Checked.append (checkChunk_sound 739584 128 c739584) (checkChunk_sound 739712 128 c739712))) (Checked.append (Checked.append (checkChunk_sound 739840 128 c739840) (checkChunk_sound 739968 128 c739968)) (Checked.append (checkChunk_sound 740096 128 c740096) (checkChunk_sound 740224 128 c740224)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 740352 128 c740352) (checkChunk_sound 740480 128 c740480)) (Checked.append (checkChunk_sound 740608 128 c740608) (checkChunk_sound 740736 128 c740736))) (Checked.append (Checked.append (checkChunk_sound 740864 128 c740864) (checkChunk_sound 740992 128 c740992)) (Checked.append (checkChunk_sound 741120 128 c741120) (checkChunk_sound 741248 128 c741248)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 741376 128 c741376) (checkChunk_sound 741504 128 c741504)) (Checked.append (checkChunk_sound 741632 128 c741632) (checkChunk_sound 741760 128 c741760))) (Checked.append (Checked.append (checkChunk_sound 741888 128 c741888) (checkChunk_sound 742016 128 c742016)) (Checked.append (checkChunk_sound 742144 128 c742144) (checkChunk_sound 742272 128 c742272)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 742400 128 c742400) (checkChunk_sound 742528 128 c742528)) (Checked.append (checkChunk_sound 742656 128 c742656) (checkChunk_sound 742784 128 c742784))) (Checked.append (Checked.append (checkChunk_sound 742912 128 c742912) (checkChunk_sound 743040 128 c743040)) (Checked.append (checkChunk_sound 743168 128 c743168) (checkChunk_sound 743296 128 c743296))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 743424 128 c743424) (checkChunk_sound 743552 128 c743552)) (Checked.append (checkChunk_sound 743680 128 c743680) (checkChunk_sound 743808 128 c743808))) (Checked.append (Checked.append (checkChunk_sound 743936 128 c743936) (checkChunk_sound 744064 128 c744064)) (Checked.append (checkChunk_sound 744192 128 c744192) (checkChunk_sound 744320 128 c744320)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 744448 128 c744448) (checkChunk_sound 744576 128 c744576)) (Checked.append (checkChunk_sound 744704 128 c744704) (checkChunk_sound 744832 128 c744832))) (Checked.append (Checked.append (checkChunk_sound 744960 128 c744960) (checkChunk_sound 745088 128 c745088)) (Checked.append (checkChunk_sound 745216 128 c745216) (checkChunk_sound 745344 128 c745344)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B011
