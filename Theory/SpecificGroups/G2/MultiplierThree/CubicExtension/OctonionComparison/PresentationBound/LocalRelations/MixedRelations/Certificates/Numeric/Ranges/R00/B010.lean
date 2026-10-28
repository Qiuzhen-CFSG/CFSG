module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [90112, 98304).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B010
private theorem c90112 : checkChunk 90112 128 = true := by decide +kernel
private theorem c90240 : checkChunk 90240 128 = true := by decide +kernel
private theorem c90368 : checkChunk 90368 128 = true := by decide +kernel
private theorem c90496 : checkChunk 90496 128 = true := by decide +kernel
private theorem c90624 : checkChunk 90624 128 = true := by decide +kernel
private theorem c90752 : checkChunk 90752 128 = true := by decide +kernel
private theorem c90880 : checkChunk 90880 128 = true := by decide +kernel
private theorem c91008 : checkChunk 91008 128 = true := by decide +kernel
private theorem c91136 : checkChunk 91136 128 = true := by decide +kernel
private theorem c91264 : checkChunk 91264 128 = true := by decide +kernel
private theorem c91392 : checkChunk 91392 128 = true := by decide +kernel
private theorem c91520 : checkChunk 91520 128 = true := by decide +kernel
private theorem c91648 : checkChunk 91648 128 = true := by decide +kernel
private theorem c91776 : checkChunk 91776 128 = true := by decide +kernel
private theorem c91904 : checkChunk 91904 128 = true := by decide +kernel
private theorem c92032 : checkChunk 92032 128 = true := by decide +kernel
private theorem c92160 : checkChunk 92160 128 = true := by decide +kernel
private theorem c92288 : checkChunk 92288 128 = true := by decide +kernel
private theorem c92416 : checkChunk 92416 128 = true := by decide +kernel
private theorem c92544 : checkChunk 92544 128 = true := by decide +kernel
private theorem c92672 : checkChunk 92672 128 = true := by decide +kernel
private theorem c92800 : checkChunk 92800 128 = true := by decide +kernel
private theorem c92928 : checkChunk 92928 128 = true := by decide +kernel
private theorem c93056 : checkChunk 93056 128 = true := by decide +kernel
private theorem c93184 : checkChunk 93184 128 = true := by decide +kernel
private theorem c93312 : checkChunk 93312 128 = true := by decide +kernel
private theorem c93440 : checkChunk 93440 128 = true := by decide +kernel
private theorem c93568 : checkChunk 93568 128 = true := by decide +kernel
private theorem c93696 : checkChunk 93696 128 = true := by decide +kernel
private theorem c93824 : checkChunk 93824 128 = true := by decide +kernel
private theorem c93952 : checkChunk 93952 128 = true := by decide +kernel
private theorem c94080 : checkChunk 94080 128 = true := by decide +kernel
private theorem c94208 : checkChunk 94208 128 = true := by decide +kernel
private theorem c94336 : checkChunk 94336 128 = true := by decide +kernel
private theorem c94464 : checkChunk 94464 128 = true := by decide +kernel
private theorem c94592 : checkChunk 94592 128 = true := by decide +kernel
private theorem c94720 : checkChunk 94720 128 = true := by decide +kernel
private theorem c94848 : checkChunk 94848 128 = true := by decide +kernel
private theorem c94976 : checkChunk 94976 128 = true := by decide +kernel
private theorem c95104 : checkChunk 95104 128 = true := by decide +kernel
private theorem c95232 : checkChunk 95232 128 = true := by decide +kernel
private theorem c95360 : checkChunk 95360 128 = true := by decide +kernel
private theorem c95488 : checkChunk 95488 128 = true := by decide +kernel
private theorem c95616 : checkChunk 95616 128 = true := by decide +kernel
private theorem c95744 : checkChunk 95744 128 = true := by decide +kernel
private theorem c95872 : checkChunk 95872 128 = true := by decide +kernel
private theorem c96000 : checkChunk 96000 128 = true := by decide +kernel
private theorem c96128 : checkChunk 96128 128 = true := by decide +kernel
private theorem c96256 : checkChunk 96256 128 = true := by decide +kernel
private theorem c96384 : checkChunk 96384 128 = true := by decide +kernel
private theorem c96512 : checkChunk 96512 128 = true := by decide +kernel
private theorem c96640 : checkChunk 96640 128 = true := by decide +kernel
private theorem c96768 : checkChunk 96768 128 = true := by decide +kernel
private theorem c96896 : checkChunk 96896 128 = true := by decide +kernel
private theorem c97024 : checkChunk 97024 128 = true := by decide +kernel
private theorem c97152 : checkChunk 97152 128 = true := by decide +kernel
private theorem c97280 : checkChunk 97280 128 = true := by decide +kernel
private theorem c97408 : checkChunk 97408 128 = true := by decide +kernel
private theorem c97536 : checkChunk 97536 128 = true := by decide +kernel
private theorem c97664 : checkChunk 97664 128 = true := by decide +kernel
private theorem c97792 : checkChunk 97792 128 = true := by decide +kernel
private theorem c97920 : checkChunk 97920 128 = true := by decide +kernel
private theorem c98048 : checkChunk 98048 128 = true := by decide +kernel
private theorem c98176 : checkChunk 98176 128 = true := by decide +kernel

public theorem checked : Checked 90112 98304 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 90112 128 c90112) (checkChunk_sound 90240 128 c90240)) (Checked.append (checkChunk_sound 90368 128 c90368) (checkChunk_sound 90496 128 c90496))) (Checked.append (Checked.append (checkChunk_sound 90624 128 c90624) (checkChunk_sound 90752 128 c90752)) (Checked.append (checkChunk_sound 90880 128 c90880) (checkChunk_sound 91008 128 c91008)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 91136 128 c91136) (checkChunk_sound 91264 128 c91264)) (Checked.append (checkChunk_sound 91392 128 c91392) (checkChunk_sound 91520 128 c91520))) (Checked.append (Checked.append (checkChunk_sound 91648 128 c91648) (checkChunk_sound 91776 128 c91776)) (Checked.append (checkChunk_sound 91904 128 c91904) (checkChunk_sound 92032 128 c92032))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 92160 128 c92160) (checkChunk_sound 92288 128 c92288)) (Checked.append (checkChunk_sound 92416 128 c92416) (checkChunk_sound 92544 128 c92544))) (Checked.append (Checked.append (checkChunk_sound 92672 128 c92672) (checkChunk_sound 92800 128 c92800)) (Checked.append (checkChunk_sound 92928 128 c92928) (checkChunk_sound 93056 128 c93056)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 93184 128 c93184) (checkChunk_sound 93312 128 c93312)) (Checked.append (checkChunk_sound 93440 128 c93440) (checkChunk_sound 93568 128 c93568))) (Checked.append (Checked.append (checkChunk_sound 93696 128 c93696) (checkChunk_sound 93824 128 c93824)) (Checked.append (checkChunk_sound 93952 128 c93952) (checkChunk_sound 94080 128 c94080)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 94208 128 c94208) (checkChunk_sound 94336 128 c94336)) (Checked.append (checkChunk_sound 94464 128 c94464) (checkChunk_sound 94592 128 c94592))) (Checked.append (Checked.append (checkChunk_sound 94720 128 c94720) (checkChunk_sound 94848 128 c94848)) (Checked.append (checkChunk_sound 94976 128 c94976) (checkChunk_sound 95104 128 c95104)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 95232 128 c95232) (checkChunk_sound 95360 128 c95360)) (Checked.append (checkChunk_sound 95488 128 c95488) (checkChunk_sound 95616 128 c95616))) (Checked.append (Checked.append (checkChunk_sound 95744 128 c95744) (checkChunk_sound 95872 128 c95872)) (Checked.append (checkChunk_sound 96000 128 c96000) (checkChunk_sound 96128 128 c96128))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 96256 128 c96256) (checkChunk_sound 96384 128 c96384)) (Checked.append (checkChunk_sound 96512 128 c96512) (checkChunk_sound 96640 128 c96640))) (Checked.append (Checked.append (checkChunk_sound 96768 128 c96768) (checkChunk_sound 96896 128 c96896)) (Checked.append (checkChunk_sound 97024 128 c97024) (checkChunk_sound 97152 128 c97152)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 97280 128 c97280) (checkChunk_sound 97408 128 c97408)) (Checked.append (checkChunk_sound 97536 128 c97536) (checkChunk_sound 97664 128 c97664))) (Checked.append (Checked.append (checkChunk_sound 97792 128 c97792) (checkChunk_sound 97920 128 c97920)) (Checked.append (checkChunk_sound 98048 128 c98048) (checkChunk_sound 98176 128 c98176)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B010
