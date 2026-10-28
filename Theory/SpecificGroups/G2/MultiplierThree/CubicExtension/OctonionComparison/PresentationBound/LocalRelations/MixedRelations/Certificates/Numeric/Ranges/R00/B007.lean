module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [65536, 73728).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B007
private theorem c65536 : checkChunk 65536 128 = true := by decide +kernel
private theorem c65664 : checkChunk 65664 128 = true := by decide +kernel
private theorem c65792 : checkChunk 65792 128 = true := by decide +kernel
private theorem c65920 : checkChunk 65920 128 = true := by decide +kernel
private theorem c66048 : checkChunk 66048 128 = true := by decide +kernel
private theorem c66176 : checkChunk 66176 128 = true := by decide +kernel
private theorem c66304 : checkChunk 66304 128 = true := by decide +kernel
private theorem c66432 : checkChunk 66432 128 = true := by decide +kernel
private theorem c66560 : checkChunk 66560 128 = true := by decide +kernel
private theorem c66688 : checkChunk 66688 128 = true := by decide +kernel
private theorem c66816 : checkChunk 66816 128 = true := by decide +kernel
private theorem c66944 : checkChunk 66944 128 = true := by decide +kernel
private theorem c67072 : checkChunk 67072 128 = true := by decide +kernel
private theorem c67200 : checkChunk 67200 128 = true := by decide +kernel
private theorem c67328 : checkChunk 67328 128 = true := by decide +kernel
private theorem c67456 : checkChunk 67456 128 = true := by decide +kernel
private theorem c67584 : checkChunk 67584 128 = true := by decide +kernel
private theorem c67712 : checkChunk 67712 128 = true := by decide +kernel
private theorem c67840 : checkChunk 67840 128 = true := by decide +kernel
private theorem c67968 : checkChunk 67968 128 = true := by decide +kernel
private theorem c68096 : checkChunk 68096 128 = true := by decide +kernel
private theorem c68224 : checkChunk 68224 128 = true := by decide +kernel
private theorem c68352 : checkChunk 68352 128 = true := by decide +kernel
private theorem c68480 : checkChunk 68480 128 = true := by decide +kernel
private theorem c68608 : checkChunk 68608 128 = true := by decide +kernel
private theorem c68736 : checkChunk 68736 128 = true := by decide +kernel
private theorem c68864 : checkChunk 68864 128 = true := by decide +kernel
private theorem c68992 : checkChunk 68992 128 = true := by decide +kernel
private theorem c69120 : checkChunk 69120 128 = true := by decide +kernel
private theorem c69248 : checkChunk 69248 128 = true := by decide +kernel
private theorem c69376 : checkChunk 69376 128 = true := by decide +kernel
private theorem c69504 : checkChunk 69504 128 = true := by decide +kernel
private theorem c69632 : checkChunk 69632 128 = true := by decide +kernel
private theorem c69760 : checkChunk 69760 128 = true := by decide +kernel
private theorem c69888 : checkChunk 69888 128 = true := by decide +kernel
private theorem c70016 : checkChunk 70016 128 = true := by decide +kernel
private theorem c70144 : checkChunk 70144 128 = true := by decide +kernel
private theorem c70272 : checkChunk 70272 128 = true := by decide +kernel
private theorem c70400 : checkChunk 70400 128 = true := by decide +kernel
private theorem c70528 : checkChunk 70528 128 = true := by decide +kernel
private theorem c70656 : checkChunk 70656 128 = true := by decide +kernel
private theorem c70784 : checkChunk 70784 128 = true := by decide +kernel
private theorem c70912 : checkChunk 70912 128 = true := by decide +kernel
private theorem c71040 : checkChunk 71040 128 = true := by decide +kernel
private theorem c71168 : checkChunk 71168 128 = true := by decide +kernel
private theorem c71296 : checkChunk 71296 128 = true := by decide +kernel
private theorem c71424 : checkChunk 71424 128 = true := by decide +kernel
private theorem c71552 : checkChunk 71552 128 = true := by decide +kernel
private theorem c71680 : checkChunk 71680 128 = true := by decide +kernel
private theorem c71808 : checkChunk 71808 128 = true := by decide +kernel
private theorem c71936 : checkChunk 71936 128 = true := by decide +kernel
private theorem c72064 : checkChunk 72064 128 = true := by decide +kernel
private theorem c72192 : checkChunk 72192 128 = true := by decide +kernel
private theorem c72320 : checkChunk 72320 128 = true := by decide +kernel
private theorem c72448 : checkChunk 72448 128 = true := by decide +kernel
private theorem c72576 : checkChunk 72576 128 = true := by decide +kernel
private theorem c72704 : checkChunk 72704 128 = true := by decide +kernel
private theorem c72832 : checkChunk 72832 128 = true := by decide +kernel
private theorem c72960 : checkChunk 72960 128 = true := by decide +kernel
private theorem c73088 : checkChunk 73088 128 = true := by decide +kernel
private theorem c73216 : checkChunk 73216 128 = true := by decide +kernel
private theorem c73344 : checkChunk 73344 128 = true := by decide +kernel
private theorem c73472 : checkChunk 73472 128 = true := by decide +kernel
private theorem c73600 : checkChunk 73600 128 = true := by decide +kernel

public theorem checked : Checked 65536 73728 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 65536 128 c65536) (checkChunk_sound 65664 128 c65664)) (Checked.append (checkChunk_sound 65792 128 c65792) (checkChunk_sound 65920 128 c65920))) (Checked.append (Checked.append (checkChunk_sound 66048 128 c66048) (checkChunk_sound 66176 128 c66176)) (Checked.append (checkChunk_sound 66304 128 c66304) (checkChunk_sound 66432 128 c66432)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 66560 128 c66560) (checkChunk_sound 66688 128 c66688)) (Checked.append (checkChunk_sound 66816 128 c66816) (checkChunk_sound 66944 128 c66944))) (Checked.append (Checked.append (checkChunk_sound 67072 128 c67072) (checkChunk_sound 67200 128 c67200)) (Checked.append (checkChunk_sound 67328 128 c67328) (checkChunk_sound 67456 128 c67456))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 67584 128 c67584) (checkChunk_sound 67712 128 c67712)) (Checked.append (checkChunk_sound 67840 128 c67840) (checkChunk_sound 67968 128 c67968))) (Checked.append (Checked.append (checkChunk_sound 68096 128 c68096) (checkChunk_sound 68224 128 c68224)) (Checked.append (checkChunk_sound 68352 128 c68352) (checkChunk_sound 68480 128 c68480)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 68608 128 c68608) (checkChunk_sound 68736 128 c68736)) (Checked.append (checkChunk_sound 68864 128 c68864) (checkChunk_sound 68992 128 c68992))) (Checked.append (Checked.append (checkChunk_sound 69120 128 c69120) (checkChunk_sound 69248 128 c69248)) (Checked.append (checkChunk_sound 69376 128 c69376) (checkChunk_sound 69504 128 c69504)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 69632 128 c69632) (checkChunk_sound 69760 128 c69760)) (Checked.append (checkChunk_sound 69888 128 c69888) (checkChunk_sound 70016 128 c70016))) (Checked.append (Checked.append (checkChunk_sound 70144 128 c70144) (checkChunk_sound 70272 128 c70272)) (Checked.append (checkChunk_sound 70400 128 c70400) (checkChunk_sound 70528 128 c70528)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 70656 128 c70656) (checkChunk_sound 70784 128 c70784)) (Checked.append (checkChunk_sound 70912 128 c70912) (checkChunk_sound 71040 128 c71040))) (Checked.append (Checked.append (checkChunk_sound 71168 128 c71168) (checkChunk_sound 71296 128 c71296)) (Checked.append (checkChunk_sound 71424 128 c71424) (checkChunk_sound 71552 128 c71552))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 71680 128 c71680) (checkChunk_sound 71808 128 c71808)) (Checked.append (checkChunk_sound 71936 128 c71936) (checkChunk_sound 72064 128 c72064))) (Checked.append (Checked.append (checkChunk_sound 72192 128 c72192) (checkChunk_sound 72320 128 c72320)) (Checked.append (checkChunk_sound 72448 128 c72448) (checkChunk_sound 72576 128 c72576)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 72704 128 c72704) (checkChunk_sound 72832 128 c72832)) (Checked.append (checkChunk_sound 72960 128 c72960) (checkChunk_sound 73088 128 c73088))) (Checked.append (Checked.append (checkChunk_sound 73216 128 c73216) (checkChunk_sound 73344 128 c73344)) (Checked.append (checkChunk_sound 73472 128 c73472) (checkChunk_sound 73600 128 c73600)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B007
