module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [827392, 835584).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B022
private theorem c827392 : checkChunk 827392 128 = true := by decide +kernel
private theorem c827520 : checkChunk 827520 128 = true := by decide +kernel
private theorem c827648 : checkChunk 827648 128 = true := by decide +kernel
private theorem c827776 : checkChunk 827776 128 = true := by decide +kernel
private theorem c827904 : checkChunk 827904 128 = true := by decide +kernel
private theorem c828032 : checkChunk 828032 128 = true := by decide +kernel
private theorem c828160 : checkChunk 828160 128 = true := by decide +kernel
private theorem c828288 : checkChunk 828288 128 = true := by decide +kernel
private theorem c828416 : checkChunk 828416 128 = true := by decide +kernel
private theorem c828544 : checkChunk 828544 128 = true := by decide +kernel
private theorem c828672 : checkChunk 828672 128 = true := by decide +kernel
private theorem c828800 : checkChunk 828800 128 = true := by decide +kernel
private theorem c828928 : checkChunk 828928 128 = true := by decide +kernel
private theorem c829056 : checkChunk 829056 128 = true := by decide +kernel
private theorem c829184 : checkChunk 829184 128 = true := by decide +kernel
private theorem c829312 : checkChunk 829312 128 = true := by decide +kernel
private theorem c829440 : checkChunk 829440 128 = true := by decide +kernel
private theorem c829568 : checkChunk 829568 128 = true := by decide +kernel
private theorem c829696 : checkChunk 829696 128 = true := by decide +kernel
private theorem c829824 : checkChunk 829824 128 = true := by decide +kernel
private theorem c829952 : checkChunk 829952 128 = true := by decide +kernel
private theorem c830080 : checkChunk 830080 128 = true := by decide +kernel
private theorem c830208 : checkChunk 830208 128 = true := by decide +kernel
private theorem c830336 : checkChunk 830336 128 = true := by decide +kernel
private theorem c830464 : checkChunk 830464 128 = true := by decide +kernel
private theorem c830592 : checkChunk 830592 128 = true := by decide +kernel
private theorem c830720 : checkChunk 830720 128 = true := by decide +kernel
private theorem c830848 : checkChunk 830848 128 = true := by decide +kernel
private theorem c830976 : checkChunk 830976 128 = true := by decide +kernel
private theorem c831104 : checkChunk 831104 128 = true := by decide +kernel
private theorem c831232 : checkChunk 831232 128 = true := by decide +kernel
private theorem c831360 : checkChunk 831360 128 = true := by decide +kernel
private theorem c831488 : checkChunk 831488 128 = true := by decide +kernel
private theorem c831616 : checkChunk 831616 128 = true := by decide +kernel
private theorem c831744 : checkChunk 831744 128 = true := by decide +kernel
private theorem c831872 : checkChunk 831872 128 = true := by decide +kernel
private theorem c832000 : checkChunk 832000 128 = true := by decide +kernel
private theorem c832128 : checkChunk 832128 128 = true := by decide +kernel
private theorem c832256 : checkChunk 832256 128 = true := by decide +kernel
private theorem c832384 : checkChunk 832384 128 = true := by decide +kernel
private theorem c832512 : checkChunk 832512 128 = true := by decide +kernel
private theorem c832640 : checkChunk 832640 128 = true := by decide +kernel
private theorem c832768 : checkChunk 832768 128 = true := by decide +kernel
private theorem c832896 : checkChunk 832896 128 = true := by decide +kernel
private theorem c833024 : checkChunk 833024 128 = true := by decide +kernel
private theorem c833152 : checkChunk 833152 128 = true := by decide +kernel
private theorem c833280 : checkChunk 833280 128 = true := by decide +kernel
private theorem c833408 : checkChunk 833408 128 = true := by decide +kernel
private theorem c833536 : checkChunk 833536 128 = true := by decide +kernel
private theorem c833664 : checkChunk 833664 128 = true := by decide +kernel
private theorem c833792 : checkChunk 833792 128 = true := by decide +kernel
private theorem c833920 : checkChunk 833920 128 = true := by decide +kernel
private theorem c834048 : checkChunk 834048 128 = true := by decide +kernel
private theorem c834176 : checkChunk 834176 128 = true := by decide +kernel
private theorem c834304 : checkChunk 834304 128 = true := by decide +kernel
private theorem c834432 : checkChunk 834432 128 = true := by decide +kernel
private theorem c834560 : checkChunk 834560 128 = true := by decide +kernel
private theorem c834688 : checkChunk 834688 128 = true := by decide +kernel
private theorem c834816 : checkChunk 834816 128 = true := by decide +kernel
private theorem c834944 : checkChunk 834944 128 = true := by decide +kernel
private theorem c835072 : checkChunk 835072 128 = true := by decide +kernel
private theorem c835200 : checkChunk 835200 128 = true := by decide +kernel
private theorem c835328 : checkChunk 835328 128 = true := by decide +kernel
private theorem c835456 : checkChunk 835456 128 = true := by decide +kernel

public theorem checked : Checked 827392 835584 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 827392 128 c827392) (checkChunk_sound 827520 128 c827520)) (Checked.append (checkChunk_sound 827648 128 c827648) (checkChunk_sound 827776 128 c827776))) (Checked.append (Checked.append (checkChunk_sound 827904 128 c827904) (checkChunk_sound 828032 128 c828032)) (Checked.append (checkChunk_sound 828160 128 c828160) (checkChunk_sound 828288 128 c828288)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 828416 128 c828416) (checkChunk_sound 828544 128 c828544)) (Checked.append (checkChunk_sound 828672 128 c828672) (checkChunk_sound 828800 128 c828800))) (Checked.append (Checked.append (checkChunk_sound 828928 128 c828928) (checkChunk_sound 829056 128 c829056)) (Checked.append (checkChunk_sound 829184 128 c829184) (checkChunk_sound 829312 128 c829312))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 829440 128 c829440) (checkChunk_sound 829568 128 c829568)) (Checked.append (checkChunk_sound 829696 128 c829696) (checkChunk_sound 829824 128 c829824))) (Checked.append (Checked.append (checkChunk_sound 829952 128 c829952) (checkChunk_sound 830080 128 c830080)) (Checked.append (checkChunk_sound 830208 128 c830208) (checkChunk_sound 830336 128 c830336)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 830464 128 c830464) (checkChunk_sound 830592 128 c830592)) (Checked.append (checkChunk_sound 830720 128 c830720) (checkChunk_sound 830848 128 c830848))) (Checked.append (Checked.append (checkChunk_sound 830976 128 c830976) (checkChunk_sound 831104 128 c831104)) (Checked.append (checkChunk_sound 831232 128 c831232) (checkChunk_sound 831360 128 c831360)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 831488 128 c831488) (checkChunk_sound 831616 128 c831616)) (Checked.append (checkChunk_sound 831744 128 c831744) (checkChunk_sound 831872 128 c831872))) (Checked.append (Checked.append (checkChunk_sound 832000 128 c832000) (checkChunk_sound 832128 128 c832128)) (Checked.append (checkChunk_sound 832256 128 c832256) (checkChunk_sound 832384 128 c832384)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 832512 128 c832512) (checkChunk_sound 832640 128 c832640)) (Checked.append (checkChunk_sound 832768 128 c832768) (checkChunk_sound 832896 128 c832896))) (Checked.append (Checked.append (checkChunk_sound 833024 128 c833024) (checkChunk_sound 833152 128 c833152)) (Checked.append (checkChunk_sound 833280 128 c833280) (checkChunk_sound 833408 128 c833408))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 833536 128 c833536) (checkChunk_sound 833664 128 c833664)) (Checked.append (checkChunk_sound 833792 128 c833792) (checkChunk_sound 833920 128 c833920))) (Checked.append (Checked.append (checkChunk_sound 834048 128 c834048) (checkChunk_sound 834176 128 c834176)) (Checked.append (checkChunk_sound 834304 128 c834304) (checkChunk_sound 834432 128 c834432)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 834560 128 c834560) (checkChunk_sound 834688 128 c834688)) (Checked.append (checkChunk_sound 834816 128 c834816) (checkChunk_sound 834944 128 c834944))) (Checked.append (Checked.append (checkChunk_sound 835072 128 c835072) (checkChunk_sound 835200 128 c835200)) (Checked.append (checkChunk_sound 835328 128 c835328) (checkChunk_sound 835456 128 c835456)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B022
