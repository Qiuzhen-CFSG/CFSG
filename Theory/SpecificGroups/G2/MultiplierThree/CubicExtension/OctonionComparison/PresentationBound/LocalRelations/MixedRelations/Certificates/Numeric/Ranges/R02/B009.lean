module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [507904, 516096).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B009
private theorem c507904 : checkChunk 507904 128 = true := by decide +kernel
private theorem c508032 : checkChunk 508032 128 = true := by decide +kernel
private theorem c508160 : checkChunk 508160 128 = true := by decide +kernel
private theorem c508288 : checkChunk 508288 128 = true := by decide +kernel
private theorem c508416 : checkChunk 508416 128 = true := by decide +kernel
private theorem c508544 : checkChunk 508544 128 = true := by decide +kernel
private theorem c508672 : checkChunk 508672 128 = true := by decide +kernel
private theorem c508800 : checkChunk 508800 128 = true := by decide +kernel
private theorem c508928 : checkChunk 508928 128 = true := by decide +kernel
private theorem c509056 : checkChunk 509056 128 = true := by decide +kernel
private theorem c509184 : checkChunk 509184 128 = true := by decide +kernel
private theorem c509312 : checkChunk 509312 128 = true := by decide +kernel
private theorem c509440 : checkChunk 509440 128 = true := by decide +kernel
private theorem c509568 : checkChunk 509568 128 = true := by decide +kernel
private theorem c509696 : checkChunk 509696 128 = true := by decide +kernel
private theorem c509824 : checkChunk 509824 128 = true := by decide +kernel
private theorem c509952 : checkChunk 509952 128 = true := by decide +kernel
private theorem c510080 : checkChunk 510080 128 = true := by decide +kernel
private theorem c510208 : checkChunk 510208 128 = true := by decide +kernel
private theorem c510336 : checkChunk 510336 128 = true := by decide +kernel
private theorem c510464 : checkChunk 510464 128 = true := by decide +kernel
private theorem c510592 : checkChunk 510592 128 = true := by decide +kernel
private theorem c510720 : checkChunk 510720 128 = true := by decide +kernel
private theorem c510848 : checkChunk 510848 128 = true := by decide +kernel
private theorem c510976 : checkChunk 510976 128 = true := by decide +kernel
private theorem c511104 : checkChunk 511104 128 = true := by decide +kernel
private theorem c511232 : checkChunk 511232 128 = true := by decide +kernel
private theorem c511360 : checkChunk 511360 128 = true := by decide +kernel
private theorem c511488 : checkChunk 511488 128 = true := by decide +kernel
private theorem c511616 : checkChunk 511616 128 = true := by decide +kernel
private theorem c511744 : checkChunk 511744 128 = true := by decide +kernel
private theorem c511872 : checkChunk 511872 128 = true := by decide +kernel
private theorem c512000 : checkChunk 512000 128 = true := by decide +kernel
private theorem c512128 : checkChunk 512128 128 = true := by decide +kernel
private theorem c512256 : checkChunk 512256 128 = true := by decide +kernel
private theorem c512384 : checkChunk 512384 128 = true := by decide +kernel
private theorem c512512 : checkChunk 512512 128 = true := by decide +kernel
private theorem c512640 : checkChunk 512640 128 = true := by decide +kernel
private theorem c512768 : checkChunk 512768 128 = true := by decide +kernel
private theorem c512896 : checkChunk 512896 128 = true := by decide +kernel
private theorem c513024 : checkChunk 513024 128 = true := by decide +kernel
private theorem c513152 : checkChunk 513152 128 = true := by decide +kernel
private theorem c513280 : checkChunk 513280 128 = true := by decide +kernel
private theorem c513408 : checkChunk 513408 128 = true := by decide +kernel
private theorem c513536 : checkChunk 513536 128 = true := by decide +kernel
private theorem c513664 : checkChunk 513664 128 = true := by decide +kernel
private theorem c513792 : checkChunk 513792 128 = true := by decide +kernel
private theorem c513920 : checkChunk 513920 128 = true := by decide +kernel
private theorem c514048 : checkChunk 514048 128 = true := by decide +kernel
private theorem c514176 : checkChunk 514176 128 = true := by decide +kernel
private theorem c514304 : checkChunk 514304 128 = true := by decide +kernel
private theorem c514432 : checkChunk 514432 128 = true := by decide +kernel
private theorem c514560 : checkChunk 514560 128 = true := by decide +kernel
private theorem c514688 : checkChunk 514688 128 = true := by decide +kernel
private theorem c514816 : checkChunk 514816 128 = true := by decide +kernel
private theorem c514944 : checkChunk 514944 128 = true := by decide +kernel
private theorem c515072 : checkChunk 515072 128 = true := by decide +kernel
private theorem c515200 : checkChunk 515200 128 = true := by decide +kernel
private theorem c515328 : checkChunk 515328 128 = true := by decide +kernel
private theorem c515456 : checkChunk 515456 128 = true := by decide +kernel
private theorem c515584 : checkChunk 515584 128 = true := by decide +kernel
private theorem c515712 : checkChunk 515712 128 = true := by decide +kernel
private theorem c515840 : checkChunk 515840 128 = true := by decide +kernel
private theorem c515968 : checkChunk 515968 128 = true := by decide +kernel

public theorem checked : Checked 507904 516096 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 507904 128 c507904) (checkChunk_sound 508032 128 c508032)) (Checked.append (checkChunk_sound 508160 128 c508160) (checkChunk_sound 508288 128 c508288))) (Checked.append (Checked.append (checkChunk_sound 508416 128 c508416) (checkChunk_sound 508544 128 c508544)) (Checked.append (checkChunk_sound 508672 128 c508672) (checkChunk_sound 508800 128 c508800)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 508928 128 c508928) (checkChunk_sound 509056 128 c509056)) (Checked.append (checkChunk_sound 509184 128 c509184) (checkChunk_sound 509312 128 c509312))) (Checked.append (Checked.append (checkChunk_sound 509440 128 c509440) (checkChunk_sound 509568 128 c509568)) (Checked.append (checkChunk_sound 509696 128 c509696) (checkChunk_sound 509824 128 c509824))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 509952 128 c509952) (checkChunk_sound 510080 128 c510080)) (Checked.append (checkChunk_sound 510208 128 c510208) (checkChunk_sound 510336 128 c510336))) (Checked.append (Checked.append (checkChunk_sound 510464 128 c510464) (checkChunk_sound 510592 128 c510592)) (Checked.append (checkChunk_sound 510720 128 c510720) (checkChunk_sound 510848 128 c510848)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 510976 128 c510976) (checkChunk_sound 511104 128 c511104)) (Checked.append (checkChunk_sound 511232 128 c511232) (checkChunk_sound 511360 128 c511360))) (Checked.append (Checked.append (checkChunk_sound 511488 128 c511488) (checkChunk_sound 511616 128 c511616)) (Checked.append (checkChunk_sound 511744 128 c511744) (checkChunk_sound 511872 128 c511872)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 512000 128 c512000) (checkChunk_sound 512128 128 c512128)) (Checked.append (checkChunk_sound 512256 128 c512256) (checkChunk_sound 512384 128 c512384))) (Checked.append (Checked.append (checkChunk_sound 512512 128 c512512) (checkChunk_sound 512640 128 c512640)) (Checked.append (checkChunk_sound 512768 128 c512768) (checkChunk_sound 512896 128 c512896)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 513024 128 c513024) (checkChunk_sound 513152 128 c513152)) (Checked.append (checkChunk_sound 513280 128 c513280) (checkChunk_sound 513408 128 c513408))) (Checked.append (Checked.append (checkChunk_sound 513536 128 c513536) (checkChunk_sound 513664 128 c513664)) (Checked.append (checkChunk_sound 513792 128 c513792) (checkChunk_sound 513920 128 c513920))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 514048 128 c514048) (checkChunk_sound 514176 128 c514176)) (Checked.append (checkChunk_sound 514304 128 c514304) (checkChunk_sound 514432 128 c514432))) (Checked.append (Checked.append (checkChunk_sound 514560 128 c514560) (checkChunk_sound 514688 128 c514688)) (Checked.append (checkChunk_sound 514816 128 c514816) (checkChunk_sound 514944 128 c514944)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 515072 128 c515072) (checkChunk_sound 515200 128 c515200)) (Checked.append (checkChunk_sound 515328 128 c515328) (checkChunk_sound 515456 128 c515456))) (Checked.append (Checked.append (checkChunk_sound 515584 128 c515584) (checkChunk_sound 515712 128 c515712)) (Checked.append (checkChunk_sound 515840 128 c515840) (checkChunk_sound 515968 128 c515968)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B009
