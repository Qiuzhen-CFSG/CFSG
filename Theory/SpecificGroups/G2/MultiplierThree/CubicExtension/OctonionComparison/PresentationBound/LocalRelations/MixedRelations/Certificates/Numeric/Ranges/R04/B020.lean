module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1024000, 1032192).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B020
private theorem c1024000 : checkChunk 1024000 128 = true := by decide +kernel
private theorem c1024128 : checkChunk 1024128 128 = true := by decide +kernel
private theorem c1024256 : checkChunk 1024256 128 = true := by decide +kernel
private theorem c1024384 : checkChunk 1024384 128 = true := by decide +kernel
private theorem c1024512 : checkChunk 1024512 128 = true := by decide +kernel
private theorem c1024640 : checkChunk 1024640 128 = true := by decide +kernel
private theorem c1024768 : checkChunk 1024768 128 = true := by decide +kernel
private theorem c1024896 : checkChunk 1024896 128 = true := by decide +kernel
private theorem c1025024 : checkChunk 1025024 128 = true := by decide +kernel
private theorem c1025152 : checkChunk 1025152 128 = true := by decide +kernel
private theorem c1025280 : checkChunk 1025280 128 = true := by decide +kernel
private theorem c1025408 : checkChunk 1025408 128 = true := by decide +kernel
private theorem c1025536 : checkChunk 1025536 128 = true := by decide +kernel
private theorem c1025664 : checkChunk 1025664 128 = true := by decide +kernel
private theorem c1025792 : checkChunk 1025792 128 = true := by decide +kernel
private theorem c1025920 : checkChunk 1025920 128 = true := by decide +kernel
private theorem c1026048 : checkChunk 1026048 128 = true := by decide +kernel
private theorem c1026176 : checkChunk 1026176 128 = true := by decide +kernel
private theorem c1026304 : checkChunk 1026304 128 = true := by decide +kernel
private theorem c1026432 : checkChunk 1026432 128 = true := by decide +kernel
private theorem c1026560 : checkChunk 1026560 128 = true := by decide +kernel
private theorem c1026688 : checkChunk 1026688 128 = true := by decide +kernel
private theorem c1026816 : checkChunk 1026816 128 = true := by decide +kernel
private theorem c1026944 : checkChunk 1026944 128 = true := by decide +kernel
private theorem c1027072 : checkChunk 1027072 128 = true := by decide +kernel
private theorem c1027200 : checkChunk 1027200 128 = true := by decide +kernel
private theorem c1027328 : checkChunk 1027328 128 = true := by decide +kernel
private theorem c1027456 : checkChunk 1027456 128 = true := by decide +kernel
private theorem c1027584 : checkChunk 1027584 128 = true := by decide +kernel
private theorem c1027712 : checkChunk 1027712 128 = true := by decide +kernel
private theorem c1027840 : checkChunk 1027840 128 = true := by decide +kernel
private theorem c1027968 : checkChunk 1027968 128 = true := by decide +kernel
private theorem c1028096 : checkChunk 1028096 128 = true := by decide +kernel
private theorem c1028224 : checkChunk 1028224 128 = true := by decide +kernel
private theorem c1028352 : checkChunk 1028352 128 = true := by decide +kernel
private theorem c1028480 : checkChunk 1028480 128 = true := by decide +kernel
private theorem c1028608 : checkChunk 1028608 128 = true := by decide +kernel
private theorem c1028736 : checkChunk 1028736 128 = true := by decide +kernel
private theorem c1028864 : checkChunk 1028864 128 = true := by decide +kernel
private theorem c1028992 : checkChunk 1028992 128 = true := by decide +kernel
private theorem c1029120 : checkChunk 1029120 128 = true := by decide +kernel
private theorem c1029248 : checkChunk 1029248 128 = true := by decide +kernel
private theorem c1029376 : checkChunk 1029376 128 = true := by decide +kernel
private theorem c1029504 : checkChunk 1029504 128 = true := by decide +kernel
private theorem c1029632 : checkChunk 1029632 128 = true := by decide +kernel
private theorem c1029760 : checkChunk 1029760 128 = true := by decide +kernel
private theorem c1029888 : checkChunk 1029888 128 = true := by decide +kernel
private theorem c1030016 : checkChunk 1030016 128 = true := by decide +kernel
private theorem c1030144 : checkChunk 1030144 128 = true := by decide +kernel
private theorem c1030272 : checkChunk 1030272 128 = true := by decide +kernel
private theorem c1030400 : checkChunk 1030400 128 = true := by decide +kernel
private theorem c1030528 : checkChunk 1030528 128 = true := by decide +kernel
private theorem c1030656 : checkChunk 1030656 128 = true := by decide +kernel
private theorem c1030784 : checkChunk 1030784 128 = true := by decide +kernel
private theorem c1030912 : checkChunk 1030912 128 = true := by decide +kernel
private theorem c1031040 : checkChunk 1031040 128 = true := by decide +kernel
private theorem c1031168 : checkChunk 1031168 128 = true := by decide +kernel
private theorem c1031296 : checkChunk 1031296 128 = true := by decide +kernel
private theorem c1031424 : checkChunk 1031424 128 = true := by decide +kernel
private theorem c1031552 : checkChunk 1031552 128 = true := by decide +kernel
private theorem c1031680 : checkChunk 1031680 128 = true := by decide +kernel
private theorem c1031808 : checkChunk 1031808 128 = true := by decide +kernel
private theorem c1031936 : checkChunk 1031936 128 = true := by decide +kernel
private theorem c1032064 : checkChunk 1032064 128 = true := by decide +kernel

public theorem checked : Checked 1024000 1032192 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1024000 128 c1024000) (checkChunk_sound 1024128 128 c1024128)) (Checked.append (checkChunk_sound 1024256 128 c1024256) (checkChunk_sound 1024384 128 c1024384))) (Checked.append (Checked.append (checkChunk_sound 1024512 128 c1024512) (checkChunk_sound 1024640 128 c1024640)) (Checked.append (checkChunk_sound 1024768 128 c1024768) (checkChunk_sound 1024896 128 c1024896)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1025024 128 c1025024) (checkChunk_sound 1025152 128 c1025152)) (Checked.append (checkChunk_sound 1025280 128 c1025280) (checkChunk_sound 1025408 128 c1025408))) (Checked.append (Checked.append (checkChunk_sound 1025536 128 c1025536) (checkChunk_sound 1025664 128 c1025664)) (Checked.append (checkChunk_sound 1025792 128 c1025792) (checkChunk_sound 1025920 128 c1025920))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1026048 128 c1026048) (checkChunk_sound 1026176 128 c1026176)) (Checked.append (checkChunk_sound 1026304 128 c1026304) (checkChunk_sound 1026432 128 c1026432))) (Checked.append (Checked.append (checkChunk_sound 1026560 128 c1026560) (checkChunk_sound 1026688 128 c1026688)) (Checked.append (checkChunk_sound 1026816 128 c1026816) (checkChunk_sound 1026944 128 c1026944)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1027072 128 c1027072) (checkChunk_sound 1027200 128 c1027200)) (Checked.append (checkChunk_sound 1027328 128 c1027328) (checkChunk_sound 1027456 128 c1027456))) (Checked.append (Checked.append (checkChunk_sound 1027584 128 c1027584) (checkChunk_sound 1027712 128 c1027712)) (Checked.append (checkChunk_sound 1027840 128 c1027840) (checkChunk_sound 1027968 128 c1027968)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1028096 128 c1028096) (checkChunk_sound 1028224 128 c1028224)) (Checked.append (checkChunk_sound 1028352 128 c1028352) (checkChunk_sound 1028480 128 c1028480))) (Checked.append (Checked.append (checkChunk_sound 1028608 128 c1028608) (checkChunk_sound 1028736 128 c1028736)) (Checked.append (checkChunk_sound 1028864 128 c1028864) (checkChunk_sound 1028992 128 c1028992)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1029120 128 c1029120) (checkChunk_sound 1029248 128 c1029248)) (Checked.append (checkChunk_sound 1029376 128 c1029376) (checkChunk_sound 1029504 128 c1029504))) (Checked.append (Checked.append (checkChunk_sound 1029632 128 c1029632) (checkChunk_sound 1029760 128 c1029760)) (Checked.append (checkChunk_sound 1029888 128 c1029888) (checkChunk_sound 1030016 128 c1030016))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1030144 128 c1030144) (checkChunk_sound 1030272 128 c1030272)) (Checked.append (checkChunk_sound 1030400 128 c1030400) (checkChunk_sound 1030528 128 c1030528))) (Checked.append (Checked.append (checkChunk_sound 1030656 128 c1030656) (checkChunk_sound 1030784 128 c1030784)) (Checked.append (checkChunk_sound 1030912 128 c1030912) (checkChunk_sound 1031040 128 c1031040)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1031168 128 c1031168) (checkChunk_sound 1031296 128 c1031296)) (Checked.append (checkChunk_sound 1031424 128 c1031424) (checkChunk_sound 1031552 128 c1031552))) (Checked.append (Checked.append (checkChunk_sound 1031680 128 c1031680) (checkChunk_sound 1031808 128 c1031808)) (Checked.append (checkChunk_sound 1031936 128 c1031936) (checkChunk_sound 1032064 128 c1032064)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B020
