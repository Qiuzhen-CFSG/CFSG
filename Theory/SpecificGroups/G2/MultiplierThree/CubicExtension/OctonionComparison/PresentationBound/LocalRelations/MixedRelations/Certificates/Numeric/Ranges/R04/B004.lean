module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [892928, 901120).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B004
private theorem c892928 : checkChunk 892928 128 = true := by decide +kernel
private theorem c893056 : checkChunk 893056 128 = true := by decide +kernel
private theorem c893184 : checkChunk 893184 128 = true := by decide +kernel
private theorem c893312 : checkChunk 893312 128 = true := by decide +kernel
private theorem c893440 : checkChunk 893440 128 = true := by decide +kernel
private theorem c893568 : checkChunk 893568 128 = true := by decide +kernel
private theorem c893696 : checkChunk 893696 128 = true := by decide +kernel
private theorem c893824 : checkChunk 893824 128 = true := by decide +kernel
private theorem c893952 : checkChunk 893952 128 = true := by decide +kernel
private theorem c894080 : checkChunk 894080 128 = true := by decide +kernel
private theorem c894208 : checkChunk 894208 128 = true := by decide +kernel
private theorem c894336 : checkChunk 894336 128 = true := by decide +kernel
private theorem c894464 : checkChunk 894464 128 = true := by decide +kernel
private theorem c894592 : checkChunk 894592 128 = true := by decide +kernel
private theorem c894720 : checkChunk 894720 128 = true := by decide +kernel
private theorem c894848 : checkChunk 894848 128 = true := by decide +kernel
private theorem c894976 : checkChunk 894976 128 = true := by decide +kernel
private theorem c895104 : checkChunk 895104 128 = true := by decide +kernel
private theorem c895232 : checkChunk 895232 128 = true := by decide +kernel
private theorem c895360 : checkChunk 895360 128 = true := by decide +kernel
private theorem c895488 : checkChunk 895488 128 = true := by decide +kernel
private theorem c895616 : checkChunk 895616 128 = true := by decide +kernel
private theorem c895744 : checkChunk 895744 128 = true := by decide +kernel
private theorem c895872 : checkChunk 895872 128 = true := by decide +kernel
private theorem c896000 : checkChunk 896000 128 = true := by decide +kernel
private theorem c896128 : checkChunk 896128 128 = true := by decide +kernel
private theorem c896256 : checkChunk 896256 128 = true := by decide +kernel
private theorem c896384 : checkChunk 896384 128 = true := by decide +kernel
private theorem c896512 : checkChunk 896512 128 = true := by decide +kernel
private theorem c896640 : checkChunk 896640 128 = true := by decide +kernel
private theorem c896768 : checkChunk 896768 128 = true := by decide +kernel
private theorem c896896 : checkChunk 896896 128 = true := by decide +kernel
private theorem c897024 : checkChunk 897024 128 = true := by decide +kernel
private theorem c897152 : checkChunk 897152 128 = true := by decide +kernel
private theorem c897280 : checkChunk 897280 128 = true := by decide +kernel
private theorem c897408 : checkChunk 897408 128 = true := by decide +kernel
private theorem c897536 : checkChunk 897536 128 = true := by decide +kernel
private theorem c897664 : checkChunk 897664 128 = true := by decide +kernel
private theorem c897792 : checkChunk 897792 128 = true := by decide +kernel
private theorem c897920 : checkChunk 897920 128 = true := by decide +kernel
private theorem c898048 : checkChunk 898048 128 = true := by decide +kernel
private theorem c898176 : checkChunk 898176 128 = true := by decide +kernel
private theorem c898304 : checkChunk 898304 128 = true := by decide +kernel
private theorem c898432 : checkChunk 898432 128 = true := by decide +kernel
private theorem c898560 : checkChunk 898560 128 = true := by decide +kernel
private theorem c898688 : checkChunk 898688 128 = true := by decide +kernel
private theorem c898816 : checkChunk 898816 128 = true := by decide +kernel
private theorem c898944 : checkChunk 898944 128 = true := by decide +kernel
private theorem c899072 : checkChunk 899072 128 = true := by decide +kernel
private theorem c899200 : checkChunk 899200 128 = true := by decide +kernel
private theorem c899328 : checkChunk 899328 128 = true := by decide +kernel
private theorem c899456 : checkChunk 899456 128 = true := by decide +kernel
private theorem c899584 : checkChunk 899584 128 = true := by decide +kernel
private theorem c899712 : checkChunk 899712 128 = true := by decide +kernel
private theorem c899840 : checkChunk 899840 128 = true := by decide +kernel
private theorem c899968 : checkChunk 899968 128 = true := by decide +kernel
private theorem c900096 : checkChunk 900096 128 = true := by decide +kernel
private theorem c900224 : checkChunk 900224 128 = true := by decide +kernel
private theorem c900352 : checkChunk 900352 128 = true := by decide +kernel
private theorem c900480 : checkChunk 900480 128 = true := by decide +kernel
private theorem c900608 : checkChunk 900608 128 = true := by decide +kernel
private theorem c900736 : checkChunk 900736 128 = true := by decide +kernel
private theorem c900864 : checkChunk 900864 128 = true := by decide +kernel
private theorem c900992 : checkChunk 900992 128 = true := by decide +kernel

public theorem checked : Checked 892928 901120 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 892928 128 c892928) (checkChunk_sound 893056 128 c893056)) (Checked.append (checkChunk_sound 893184 128 c893184) (checkChunk_sound 893312 128 c893312))) (Checked.append (Checked.append (checkChunk_sound 893440 128 c893440) (checkChunk_sound 893568 128 c893568)) (Checked.append (checkChunk_sound 893696 128 c893696) (checkChunk_sound 893824 128 c893824)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 893952 128 c893952) (checkChunk_sound 894080 128 c894080)) (Checked.append (checkChunk_sound 894208 128 c894208) (checkChunk_sound 894336 128 c894336))) (Checked.append (Checked.append (checkChunk_sound 894464 128 c894464) (checkChunk_sound 894592 128 c894592)) (Checked.append (checkChunk_sound 894720 128 c894720) (checkChunk_sound 894848 128 c894848))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 894976 128 c894976) (checkChunk_sound 895104 128 c895104)) (Checked.append (checkChunk_sound 895232 128 c895232) (checkChunk_sound 895360 128 c895360))) (Checked.append (Checked.append (checkChunk_sound 895488 128 c895488) (checkChunk_sound 895616 128 c895616)) (Checked.append (checkChunk_sound 895744 128 c895744) (checkChunk_sound 895872 128 c895872)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 896000 128 c896000) (checkChunk_sound 896128 128 c896128)) (Checked.append (checkChunk_sound 896256 128 c896256) (checkChunk_sound 896384 128 c896384))) (Checked.append (Checked.append (checkChunk_sound 896512 128 c896512) (checkChunk_sound 896640 128 c896640)) (Checked.append (checkChunk_sound 896768 128 c896768) (checkChunk_sound 896896 128 c896896)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 897024 128 c897024) (checkChunk_sound 897152 128 c897152)) (Checked.append (checkChunk_sound 897280 128 c897280) (checkChunk_sound 897408 128 c897408))) (Checked.append (Checked.append (checkChunk_sound 897536 128 c897536) (checkChunk_sound 897664 128 c897664)) (Checked.append (checkChunk_sound 897792 128 c897792) (checkChunk_sound 897920 128 c897920)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 898048 128 c898048) (checkChunk_sound 898176 128 c898176)) (Checked.append (checkChunk_sound 898304 128 c898304) (checkChunk_sound 898432 128 c898432))) (Checked.append (Checked.append (checkChunk_sound 898560 128 c898560) (checkChunk_sound 898688 128 c898688)) (Checked.append (checkChunk_sound 898816 128 c898816) (checkChunk_sound 898944 128 c898944))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 899072 128 c899072) (checkChunk_sound 899200 128 c899200)) (Checked.append (checkChunk_sound 899328 128 c899328) (checkChunk_sound 899456 128 c899456))) (Checked.append (Checked.append (checkChunk_sound 899584 128 c899584) (checkChunk_sound 899712 128 c899712)) (Checked.append (checkChunk_sound 899840 128 c899840) (checkChunk_sound 899968 128 c899968)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 900096 128 c900096) (checkChunk_sound 900224 128 c900224)) (Checked.append (checkChunk_sound 900352 128 c900352) (checkChunk_sound 900480 128 c900480))) (Checked.append (Checked.append (checkChunk_sound 900608 128 c900608) (checkChunk_sound 900736 128 c900736)) (Checked.append (checkChunk_sound 900864 128 c900864) (checkChunk_sound 900992 128 c900992)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04.B004
