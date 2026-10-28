module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [638976, 647168).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B025
private theorem c638976 : checkChunk 638976 128 = true := by decide +kernel
private theorem c639104 : checkChunk 639104 128 = true := by decide +kernel
private theorem c639232 : checkChunk 639232 128 = true := by decide +kernel
private theorem c639360 : checkChunk 639360 128 = true := by decide +kernel
private theorem c639488 : checkChunk 639488 128 = true := by decide +kernel
private theorem c639616 : checkChunk 639616 128 = true := by decide +kernel
private theorem c639744 : checkChunk 639744 128 = true := by decide +kernel
private theorem c639872 : checkChunk 639872 128 = true := by decide +kernel
private theorem c640000 : checkChunk 640000 128 = true := by decide +kernel
private theorem c640128 : checkChunk 640128 128 = true := by decide +kernel
private theorem c640256 : checkChunk 640256 128 = true := by decide +kernel
private theorem c640384 : checkChunk 640384 128 = true := by decide +kernel
private theorem c640512 : checkChunk 640512 128 = true := by decide +kernel
private theorem c640640 : checkChunk 640640 128 = true := by decide +kernel
private theorem c640768 : checkChunk 640768 128 = true := by decide +kernel
private theorem c640896 : checkChunk 640896 128 = true := by decide +kernel
private theorem c641024 : checkChunk 641024 128 = true := by decide +kernel
private theorem c641152 : checkChunk 641152 128 = true := by decide +kernel
private theorem c641280 : checkChunk 641280 128 = true := by decide +kernel
private theorem c641408 : checkChunk 641408 128 = true := by decide +kernel
private theorem c641536 : checkChunk 641536 128 = true := by decide +kernel
private theorem c641664 : checkChunk 641664 128 = true := by decide +kernel
private theorem c641792 : checkChunk 641792 128 = true := by decide +kernel
private theorem c641920 : checkChunk 641920 128 = true := by decide +kernel
private theorem c642048 : checkChunk 642048 128 = true := by decide +kernel
private theorem c642176 : checkChunk 642176 128 = true := by decide +kernel
private theorem c642304 : checkChunk 642304 128 = true := by decide +kernel
private theorem c642432 : checkChunk 642432 128 = true := by decide +kernel
private theorem c642560 : checkChunk 642560 128 = true := by decide +kernel
private theorem c642688 : checkChunk 642688 128 = true := by decide +kernel
private theorem c642816 : checkChunk 642816 128 = true := by decide +kernel
private theorem c642944 : checkChunk 642944 128 = true := by decide +kernel
private theorem c643072 : checkChunk 643072 128 = true := by decide +kernel
private theorem c643200 : checkChunk 643200 128 = true := by decide +kernel
private theorem c643328 : checkChunk 643328 128 = true := by decide +kernel
private theorem c643456 : checkChunk 643456 128 = true := by decide +kernel
private theorem c643584 : checkChunk 643584 128 = true := by decide +kernel
private theorem c643712 : checkChunk 643712 128 = true := by decide +kernel
private theorem c643840 : checkChunk 643840 128 = true := by decide +kernel
private theorem c643968 : checkChunk 643968 128 = true := by decide +kernel
private theorem c644096 : checkChunk 644096 128 = true := by decide +kernel
private theorem c644224 : checkChunk 644224 128 = true := by decide +kernel
private theorem c644352 : checkChunk 644352 128 = true := by decide +kernel
private theorem c644480 : checkChunk 644480 128 = true := by decide +kernel
private theorem c644608 : checkChunk 644608 128 = true := by decide +kernel
private theorem c644736 : checkChunk 644736 128 = true := by decide +kernel
private theorem c644864 : checkChunk 644864 128 = true := by decide +kernel
private theorem c644992 : checkChunk 644992 128 = true := by decide +kernel
private theorem c645120 : checkChunk 645120 128 = true := by decide +kernel
private theorem c645248 : checkChunk 645248 128 = true := by decide +kernel
private theorem c645376 : checkChunk 645376 128 = true := by decide +kernel
private theorem c645504 : checkChunk 645504 128 = true := by decide +kernel
private theorem c645632 : checkChunk 645632 128 = true := by decide +kernel
private theorem c645760 : checkChunk 645760 128 = true := by decide +kernel
private theorem c645888 : checkChunk 645888 128 = true := by decide +kernel
private theorem c646016 : checkChunk 646016 128 = true := by decide +kernel
private theorem c646144 : checkChunk 646144 128 = true := by decide +kernel
private theorem c646272 : checkChunk 646272 128 = true := by decide +kernel
private theorem c646400 : checkChunk 646400 128 = true := by decide +kernel
private theorem c646528 : checkChunk 646528 128 = true := by decide +kernel
private theorem c646656 : checkChunk 646656 128 = true := by decide +kernel
private theorem c646784 : checkChunk 646784 128 = true := by decide +kernel
private theorem c646912 : checkChunk 646912 128 = true := by decide +kernel
private theorem c647040 : checkChunk 647040 128 = true := by decide +kernel

public theorem checked : Checked 638976 647168 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 638976 128 c638976) (checkChunk_sound 639104 128 c639104)) (Checked.append (checkChunk_sound 639232 128 c639232) (checkChunk_sound 639360 128 c639360))) (Checked.append (Checked.append (checkChunk_sound 639488 128 c639488) (checkChunk_sound 639616 128 c639616)) (Checked.append (checkChunk_sound 639744 128 c639744) (checkChunk_sound 639872 128 c639872)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 640000 128 c640000) (checkChunk_sound 640128 128 c640128)) (Checked.append (checkChunk_sound 640256 128 c640256) (checkChunk_sound 640384 128 c640384))) (Checked.append (Checked.append (checkChunk_sound 640512 128 c640512) (checkChunk_sound 640640 128 c640640)) (Checked.append (checkChunk_sound 640768 128 c640768) (checkChunk_sound 640896 128 c640896))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 641024 128 c641024) (checkChunk_sound 641152 128 c641152)) (Checked.append (checkChunk_sound 641280 128 c641280) (checkChunk_sound 641408 128 c641408))) (Checked.append (Checked.append (checkChunk_sound 641536 128 c641536) (checkChunk_sound 641664 128 c641664)) (Checked.append (checkChunk_sound 641792 128 c641792) (checkChunk_sound 641920 128 c641920)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 642048 128 c642048) (checkChunk_sound 642176 128 c642176)) (Checked.append (checkChunk_sound 642304 128 c642304) (checkChunk_sound 642432 128 c642432))) (Checked.append (Checked.append (checkChunk_sound 642560 128 c642560) (checkChunk_sound 642688 128 c642688)) (Checked.append (checkChunk_sound 642816 128 c642816) (checkChunk_sound 642944 128 c642944)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 643072 128 c643072) (checkChunk_sound 643200 128 c643200)) (Checked.append (checkChunk_sound 643328 128 c643328) (checkChunk_sound 643456 128 c643456))) (Checked.append (Checked.append (checkChunk_sound 643584 128 c643584) (checkChunk_sound 643712 128 c643712)) (Checked.append (checkChunk_sound 643840 128 c643840) (checkChunk_sound 643968 128 c643968)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 644096 128 c644096) (checkChunk_sound 644224 128 c644224)) (Checked.append (checkChunk_sound 644352 128 c644352) (checkChunk_sound 644480 128 c644480))) (Checked.append (Checked.append (checkChunk_sound 644608 128 c644608) (checkChunk_sound 644736 128 c644736)) (Checked.append (checkChunk_sound 644864 128 c644864) (checkChunk_sound 644992 128 c644992))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 645120 128 c645120) (checkChunk_sound 645248 128 c645248)) (Checked.append (checkChunk_sound 645376 128 c645376) (checkChunk_sound 645504 128 c645504))) (Checked.append (Checked.append (checkChunk_sound 645632 128 c645632) (checkChunk_sound 645760 128 c645760)) (Checked.append (checkChunk_sound 645888 128 c645888) (checkChunk_sound 646016 128 c646016)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 646144 128 c646144) (checkChunk_sound 646272 128 c646272)) (Checked.append (checkChunk_sound 646400 128 c646400) (checkChunk_sound 646528 128 c646528))) (Checked.append (Checked.append (checkChunk_sound 646656 128 c646656) (checkChunk_sound 646784 128 c646784)) (Checked.append (checkChunk_sound 646912 128 c646912) (checkChunk_sound 647040 128 c647040)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B025
