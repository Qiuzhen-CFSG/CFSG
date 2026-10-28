module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [196608, 204800).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B023
private theorem c196608 : checkChunk 196608 128 = true := by decide +kernel
private theorem c196736 : checkChunk 196736 128 = true := by decide +kernel
private theorem c196864 : checkChunk 196864 128 = true := by decide +kernel
private theorem c196992 : checkChunk 196992 128 = true := by decide +kernel
private theorem c197120 : checkChunk 197120 128 = true := by decide +kernel
private theorem c197248 : checkChunk 197248 128 = true := by decide +kernel
private theorem c197376 : checkChunk 197376 128 = true := by decide +kernel
private theorem c197504 : checkChunk 197504 128 = true := by decide +kernel
private theorem c197632 : checkChunk 197632 128 = true := by decide +kernel
private theorem c197760 : checkChunk 197760 128 = true := by decide +kernel
private theorem c197888 : checkChunk 197888 128 = true := by decide +kernel
private theorem c198016 : checkChunk 198016 128 = true := by decide +kernel
private theorem c198144 : checkChunk 198144 128 = true := by decide +kernel
private theorem c198272 : checkChunk 198272 128 = true := by decide +kernel
private theorem c198400 : checkChunk 198400 128 = true := by decide +kernel
private theorem c198528 : checkChunk 198528 128 = true := by decide +kernel
private theorem c198656 : checkChunk 198656 128 = true := by decide +kernel
private theorem c198784 : checkChunk 198784 128 = true := by decide +kernel
private theorem c198912 : checkChunk 198912 128 = true := by decide +kernel
private theorem c199040 : checkChunk 199040 128 = true := by decide +kernel
private theorem c199168 : checkChunk 199168 128 = true := by decide +kernel
private theorem c199296 : checkChunk 199296 128 = true := by decide +kernel
private theorem c199424 : checkChunk 199424 128 = true := by decide +kernel
private theorem c199552 : checkChunk 199552 128 = true := by decide +kernel
private theorem c199680 : checkChunk 199680 128 = true := by decide +kernel
private theorem c199808 : checkChunk 199808 128 = true := by decide +kernel
private theorem c199936 : checkChunk 199936 128 = true := by decide +kernel
private theorem c200064 : checkChunk 200064 128 = true := by decide +kernel
private theorem c200192 : checkChunk 200192 128 = true := by decide +kernel
private theorem c200320 : checkChunk 200320 128 = true := by decide +kernel
private theorem c200448 : checkChunk 200448 128 = true := by decide +kernel
private theorem c200576 : checkChunk 200576 128 = true := by decide +kernel
private theorem c200704 : checkChunk 200704 128 = true := by decide +kernel
private theorem c200832 : checkChunk 200832 128 = true := by decide +kernel
private theorem c200960 : checkChunk 200960 128 = true := by decide +kernel
private theorem c201088 : checkChunk 201088 128 = true := by decide +kernel
private theorem c201216 : checkChunk 201216 128 = true := by decide +kernel
private theorem c201344 : checkChunk 201344 128 = true := by decide +kernel
private theorem c201472 : checkChunk 201472 128 = true := by decide +kernel
private theorem c201600 : checkChunk 201600 128 = true := by decide +kernel
private theorem c201728 : checkChunk 201728 128 = true := by decide +kernel
private theorem c201856 : checkChunk 201856 128 = true := by decide +kernel
private theorem c201984 : checkChunk 201984 128 = true := by decide +kernel
private theorem c202112 : checkChunk 202112 128 = true := by decide +kernel
private theorem c202240 : checkChunk 202240 128 = true := by decide +kernel
private theorem c202368 : checkChunk 202368 128 = true := by decide +kernel
private theorem c202496 : checkChunk 202496 128 = true := by decide +kernel
private theorem c202624 : checkChunk 202624 128 = true := by decide +kernel
private theorem c202752 : checkChunk 202752 128 = true := by decide +kernel
private theorem c202880 : checkChunk 202880 128 = true := by decide +kernel
private theorem c203008 : checkChunk 203008 128 = true := by decide +kernel
private theorem c203136 : checkChunk 203136 128 = true := by decide +kernel
private theorem c203264 : checkChunk 203264 128 = true := by decide +kernel
private theorem c203392 : checkChunk 203392 128 = true := by decide +kernel
private theorem c203520 : checkChunk 203520 128 = true := by decide +kernel
private theorem c203648 : checkChunk 203648 128 = true := by decide +kernel
private theorem c203776 : checkChunk 203776 128 = true := by decide +kernel
private theorem c203904 : checkChunk 203904 128 = true := by decide +kernel
private theorem c204032 : checkChunk 204032 128 = true := by decide +kernel
private theorem c204160 : checkChunk 204160 128 = true := by decide +kernel
private theorem c204288 : checkChunk 204288 128 = true := by decide +kernel
private theorem c204416 : checkChunk 204416 128 = true := by decide +kernel
private theorem c204544 : checkChunk 204544 128 = true := by decide +kernel
private theorem c204672 : checkChunk 204672 128 = true := by decide +kernel

public theorem checked : Checked 196608 204800 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 196608 128 c196608) (checkChunk_sound 196736 128 c196736)) (Checked.append (checkChunk_sound 196864 128 c196864) (checkChunk_sound 196992 128 c196992))) (Checked.append (Checked.append (checkChunk_sound 197120 128 c197120) (checkChunk_sound 197248 128 c197248)) (Checked.append (checkChunk_sound 197376 128 c197376) (checkChunk_sound 197504 128 c197504)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 197632 128 c197632) (checkChunk_sound 197760 128 c197760)) (Checked.append (checkChunk_sound 197888 128 c197888) (checkChunk_sound 198016 128 c198016))) (Checked.append (Checked.append (checkChunk_sound 198144 128 c198144) (checkChunk_sound 198272 128 c198272)) (Checked.append (checkChunk_sound 198400 128 c198400) (checkChunk_sound 198528 128 c198528))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 198656 128 c198656) (checkChunk_sound 198784 128 c198784)) (Checked.append (checkChunk_sound 198912 128 c198912) (checkChunk_sound 199040 128 c199040))) (Checked.append (Checked.append (checkChunk_sound 199168 128 c199168) (checkChunk_sound 199296 128 c199296)) (Checked.append (checkChunk_sound 199424 128 c199424) (checkChunk_sound 199552 128 c199552)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 199680 128 c199680) (checkChunk_sound 199808 128 c199808)) (Checked.append (checkChunk_sound 199936 128 c199936) (checkChunk_sound 200064 128 c200064))) (Checked.append (Checked.append (checkChunk_sound 200192 128 c200192) (checkChunk_sound 200320 128 c200320)) (Checked.append (checkChunk_sound 200448 128 c200448) (checkChunk_sound 200576 128 c200576)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 200704 128 c200704) (checkChunk_sound 200832 128 c200832)) (Checked.append (checkChunk_sound 200960 128 c200960) (checkChunk_sound 201088 128 c201088))) (Checked.append (Checked.append (checkChunk_sound 201216 128 c201216) (checkChunk_sound 201344 128 c201344)) (Checked.append (checkChunk_sound 201472 128 c201472) (checkChunk_sound 201600 128 c201600)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 201728 128 c201728) (checkChunk_sound 201856 128 c201856)) (Checked.append (checkChunk_sound 201984 128 c201984) (checkChunk_sound 202112 128 c202112))) (Checked.append (Checked.append (checkChunk_sound 202240 128 c202240) (checkChunk_sound 202368 128 c202368)) (Checked.append (checkChunk_sound 202496 128 c202496) (checkChunk_sound 202624 128 c202624))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 202752 128 c202752) (checkChunk_sound 202880 128 c202880)) (Checked.append (checkChunk_sound 203008 128 c203008) (checkChunk_sound 203136 128 c203136))) (Checked.append (Checked.append (checkChunk_sound 203264 128 c203264) (checkChunk_sound 203392 128 c203392)) (Checked.append (checkChunk_sound 203520 128 c203520) (checkChunk_sound 203648 128 c203648)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 203776 128 c203776) (checkChunk_sound 203904 128 c203904)) (Checked.append (checkChunk_sound 204032 128 c204032) (checkChunk_sound 204160 128 c204160))) (Checked.append (Checked.append (checkChunk_sound 204288 128 c204288) (checkChunk_sound 204416 128 c204416)) (Checked.append (checkChunk_sound 204544 128 c204544) (checkChunk_sound 204672 128 c204672)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B023
