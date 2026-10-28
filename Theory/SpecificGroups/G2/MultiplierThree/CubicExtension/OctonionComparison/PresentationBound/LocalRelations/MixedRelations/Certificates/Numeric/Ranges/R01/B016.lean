module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [352256, 360448).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B016
private theorem c352256 : checkChunk 352256 128 = true := by decide +kernel
private theorem c352384 : checkChunk 352384 128 = true := by decide +kernel
private theorem c352512 : checkChunk 352512 128 = true := by decide +kernel
private theorem c352640 : checkChunk 352640 128 = true := by decide +kernel
private theorem c352768 : checkChunk 352768 128 = true := by decide +kernel
private theorem c352896 : checkChunk 352896 128 = true := by decide +kernel
private theorem c353024 : checkChunk 353024 128 = true := by decide +kernel
private theorem c353152 : checkChunk 353152 128 = true := by decide +kernel
private theorem c353280 : checkChunk 353280 128 = true := by decide +kernel
private theorem c353408 : checkChunk 353408 128 = true := by decide +kernel
private theorem c353536 : checkChunk 353536 128 = true := by decide +kernel
private theorem c353664 : checkChunk 353664 128 = true := by decide +kernel
private theorem c353792 : checkChunk 353792 128 = true := by decide +kernel
private theorem c353920 : checkChunk 353920 128 = true := by decide +kernel
private theorem c354048 : checkChunk 354048 128 = true := by decide +kernel
private theorem c354176 : checkChunk 354176 128 = true := by decide +kernel
private theorem c354304 : checkChunk 354304 128 = true := by decide +kernel
private theorem c354432 : checkChunk 354432 128 = true := by decide +kernel
private theorem c354560 : checkChunk 354560 128 = true := by decide +kernel
private theorem c354688 : checkChunk 354688 128 = true := by decide +kernel
private theorem c354816 : checkChunk 354816 128 = true := by decide +kernel
private theorem c354944 : checkChunk 354944 128 = true := by decide +kernel
private theorem c355072 : checkChunk 355072 128 = true := by decide +kernel
private theorem c355200 : checkChunk 355200 128 = true := by decide +kernel
private theorem c355328 : checkChunk 355328 128 = true := by decide +kernel
private theorem c355456 : checkChunk 355456 128 = true := by decide +kernel
private theorem c355584 : checkChunk 355584 128 = true := by decide +kernel
private theorem c355712 : checkChunk 355712 128 = true := by decide +kernel
private theorem c355840 : checkChunk 355840 128 = true := by decide +kernel
private theorem c355968 : checkChunk 355968 128 = true := by decide +kernel
private theorem c356096 : checkChunk 356096 128 = true := by decide +kernel
private theorem c356224 : checkChunk 356224 128 = true := by decide +kernel
private theorem c356352 : checkChunk 356352 128 = true := by decide +kernel
private theorem c356480 : checkChunk 356480 128 = true := by decide +kernel
private theorem c356608 : checkChunk 356608 128 = true := by decide +kernel
private theorem c356736 : checkChunk 356736 128 = true := by decide +kernel
private theorem c356864 : checkChunk 356864 128 = true := by decide +kernel
private theorem c356992 : checkChunk 356992 128 = true := by decide +kernel
private theorem c357120 : checkChunk 357120 128 = true := by decide +kernel
private theorem c357248 : checkChunk 357248 128 = true := by decide +kernel
private theorem c357376 : checkChunk 357376 128 = true := by decide +kernel
private theorem c357504 : checkChunk 357504 128 = true := by decide +kernel
private theorem c357632 : checkChunk 357632 128 = true := by decide +kernel
private theorem c357760 : checkChunk 357760 128 = true := by decide +kernel
private theorem c357888 : checkChunk 357888 128 = true := by decide +kernel
private theorem c358016 : checkChunk 358016 128 = true := by decide +kernel
private theorem c358144 : checkChunk 358144 128 = true := by decide +kernel
private theorem c358272 : checkChunk 358272 128 = true := by decide +kernel
private theorem c358400 : checkChunk 358400 128 = true := by decide +kernel
private theorem c358528 : checkChunk 358528 128 = true := by decide +kernel
private theorem c358656 : checkChunk 358656 128 = true := by decide +kernel
private theorem c358784 : checkChunk 358784 128 = true := by decide +kernel
private theorem c358912 : checkChunk 358912 128 = true := by decide +kernel
private theorem c359040 : checkChunk 359040 128 = true := by decide +kernel
private theorem c359168 : checkChunk 359168 128 = true := by decide +kernel
private theorem c359296 : checkChunk 359296 128 = true := by decide +kernel
private theorem c359424 : checkChunk 359424 128 = true := by decide +kernel
private theorem c359552 : checkChunk 359552 128 = true := by decide +kernel
private theorem c359680 : checkChunk 359680 128 = true := by decide +kernel
private theorem c359808 : checkChunk 359808 128 = true := by decide +kernel
private theorem c359936 : checkChunk 359936 128 = true := by decide +kernel
private theorem c360064 : checkChunk 360064 128 = true := by decide +kernel
private theorem c360192 : checkChunk 360192 128 = true := by decide +kernel
private theorem c360320 : checkChunk 360320 128 = true := by decide +kernel

public theorem checked : Checked 352256 360448 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 352256 128 c352256) (checkChunk_sound 352384 128 c352384)) (Checked.append (checkChunk_sound 352512 128 c352512) (checkChunk_sound 352640 128 c352640))) (Checked.append (Checked.append (checkChunk_sound 352768 128 c352768) (checkChunk_sound 352896 128 c352896)) (Checked.append (checkChunk_sound 353024 128 c353024) (checkChunk_sound 353152 128 c353152)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 353280 128 c353280) (checkChunk_sound 353408 128 c353408)) (Checked.append (checkChunk_sound 353536 128 c353536) (checkChunk_sound 353664 128 c353664))) (Checked.append (Checked.append (checkChunk_sound 353792 128 c353792) (checkChunk_sound 353920 128 c353920)) (Checked.append (checkChunk_sound 354048 128 c354048) (checkChunk_sound 354176 128 c354176))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 354304 128 c354304) (checkChunk_sound 354432 128 c354432)) (Checked.append (checkChunk_sound 354560 128 c354560) (checkChunk_sound 354688 128 c354688))) (Checked.append (Checked.append (checkChunk_sound 354816 128 c354816) (checkChunk_sound 354944 128 c354944)) (Checked.append (checkChunk_sound 355072 128 c355072) (checkChunk_sound 355200 128 c355200)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 355328 128 c355328) (checkChunk_sound 355456 128 c355456)) (Checked.append (checkChunk_sound 355584 128 c355584) (checkChunk_sound 355712 128 c355712))) (Checked.append (Checked.append (checkChunk_sound 355840 128 c355840) (checkChunk_sound 355968 128 c355968)) (Checked.append (checkChunk_sound 356096 128 c356096) (checkChunk_sound 356224 128 c356224)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 356352 128 c356352) (checkChunk_sound 356480 128 c356480)) (Checked.append (checkChunk_sound 356608 128 c356608) (checkChunk_sound 356736 128 c356736))) (Checked.append (Checked.append (checkChunk_sound 356864 128 c356864) (checkChunk_sound 356992 128 c356992)) (Checked.append (checkChunk_sound 357120 128 c357120) (checkChunk_sound 357248 128 c357248)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 357376 128 c357376) (checkChunk_sound 357504 128 c357504)) (Checked.append (checkChunk_sound 357632 128 c357632) (checkChunk_sound 357760 128 c357760))) (Checked.append (Checked.append (checkChunk_sound 357888 128 c357888) (checkChunk_sound 358016 128 c358016)) (Checked.append (checkChunk_sound 358144 128 c358144) (checkChunk_sound 358272 128 c358272))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 358400 128 c358400) (checkChunk_sound 358528 128 c358528)) (Checked.append (checkChunk_sound 358656 128 c358656) (checkChunk_sound 358784 128 c358784))) (Checked.append (Checked.append (checkChunk_sound 358912 128 c358912) (checkChunk_sound 359040 128 c359040)) (Checked.append (checkChunk_sound 359168 128 c359168) (checkChunk_sound 359296 128 c359296)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 359424 128 c359424) (checkChunk_sound 359552 128 c359552)) (Checked.append (checkChunk_sound 359680 128 c359680) (checkChunk_sound 359808 128 c359808))) (Checked.append (Checked.append (checkChunk_sound 359936 128 c359936) (checkChunk_sound 360064 128 c360064)) (Checked.append (checkChunk_sound 360192 128 c360192) (checkChunk_sound 360320 128 c360320)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B016
