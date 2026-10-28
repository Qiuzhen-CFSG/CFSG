module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1703936, 1712128).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B025
private theorem c1703936 : checkChunk 1703936 128 = true := by decide +kernel
private theorem c1704064 : checkChunk 1704064 128 = true := by decide +kernel
private theorem c1704192 : checkChunk 1704192 128 = true := by decide +kernel
private theorem c1704320 : checkChunk 1704320 128 = true := by decide +kernel
private theorem c1704448 : checkChunk 1704448 128 = true := by decide +kernel
private theorem c1704576 : checkChunk 1704576 128 = true := by decide +kernel
private theorem c1704704 : checkChunk 1704704 128 = true := by decide +kernel
private theorem c1704832 : checkChunk 1704832 128 = true := by decide +kernel
private theorem c1704960 : checkChunk 1704960 128 = true := by decide +kernel
private theorem c1705088 : checkChunk 1705088 128 = true := by decide +kernel
private theorem c1705216 : checkChunk 1705216 128 = true := by decide +kernel
private theorem c1705344 : checkChunk 1705344 128 = true := by decide +kernel
private theorem c1705472 : checkChunk 1705472 128 = true := by decide +kernel
private theorem c1705600 : checkChunk 1705600 128 = true := by decide +kernel
private theorem c1705728 : checkChunk 1705728 128 = true := by decide +kernel
private theorem c1705856 : checkChunk 1705856 128 = true := by decide +kernel
private theorem c1705984 : checkChunk 1705984 128 = true := by decide +kernel
private theorem c1706112 : checkChunk 1706112 128 = true := by decide +kernel
private theorem c1706240 : checkChunk 1706240 128 = true := by decide +kernel
private theorem c1706368 : checkChunk 1706368 128 = true := by decide +kernel
private theorem c1706496 : checkChunk 1706496 128 = true := by decide +kernel
private theorem c1706624 : checkChunk 1706624 128 = true := by decide +kernel
private theorem c1706752 : checkChunk 1706752 128 = true := by decide +kernel
private theorem c1706880 : checkChunk 1706880 128 = true := by decide +kernel
private theorem c1707008 : checkChunk 1707008 128 = true := by decide +kernel
private theorem c1707136 : checkChunk 1707136 128 = true := by decide +kernel
private theorem c1707264 : checkChunk 1707264 128 = true := by decide +kernel
private theorem c1707392 : checkChunk 1707392 128 = true := by decide +kernel
private theorem c1707520 : checkChunk 1707520 128 = true := by decide +kernel
private theorem c1707648 : checkChunk 1707648 128 = true := by decide +kernel
private theorem c1707776 : checkChunk 1707776 128 = true := by decide +kernel
private theorem c1707904 : checkChunk 1707904 128 = true := by decide +kernel
private theorem c1708032 : checkChunk 1708032 128 = true := by decide +kernel
private theorem c1708160 : checkChunk 1708160 128 = true := by decide +kernel
private theorem c1708288 : checkChunk 1708288 128 = true := by decide +kernel
private theorem c1708416 : checkChunk 1708416 128 = true := by decide +kernel
private theorem c1708544 : checkChunk 1708544 128 = true := by decide +kernel
private theorem c1708672 : checkChunk 1708672 128 = true := by decide +kernel
private theorem c1708800 : checkChunk 1708800 128 = true := by decide +kernel
private theorem c1708928 : checkChunk 1708928 128 = true := by decide +kernel
private theorem c1709056 : checkChunk 1709056 128 = true := by decide +kernel
private theorem c1709184 : checkChunk 1709184 128 = true := by decide +kernel
private theorem c1709312 : checkChunk 1709312 128 = true := by decide +kernel
private theorem c1709440 : checkChunk 1709440 128 = true := by decide +kernel
private theorem c1709568 : checkChunk 1709568 128 = true := by decide +kernel
private theorem c1709696 : checkChunk 1709696 128 = true := by decide +kernel
private theorem c1709824 : checkChunk 1709824 128 = true := by decide +kernel
private theorem c1709952 : checkChunk 1709952 128 = true := by decide +kernel
private theorem c1710080 : checkChunk 1710080 128 = true := by decide +kernel
private theorem c1710208 : checkChunk 1710208 128 = true := by decide +kernel
private theorem c1710336 : checkChunk 1710336 128 = true := by decide +kernel
private theorem c1710464 : checkChunk 1710464 128 = true := by decide +kernel
private theorem c1710592 : checkChunk 1710592 128 = true := by decide +kernel
private theorem c1710720 : checkChunk 1710720 128 = true := by decide +kernel
private theorem c1710848 : checkChunk 1710848 128 = true := by decide +kernel
private theorem c1710976 : checkChunk 1710976 128 = true := by decide +kernel
private theorem c1711104 : checkChunk 1711104 128 = true := by decide +kernel
private theorem c1711232 : checkChunk 1711232 128 = true := by decide +kernel
private theorem c1711360 : checkChunk 1711360 128 = true := by decide +kernel
private theorem c1711488 : checkChunk 1711488 128 = true := by decide +kernel
private theorem c1711616 : checkChunk 1711616 128 = true := by decide +kernel
private theorem c1711744 : checkChunk 1711744 128 = true := by decide +kernel
private theorem c1711872 : checkChunk 1711872 128 = true := by decide +kernel
private theorem c1712000 : checkChunk 1712000 128 = true := by decide +kernel

public theorem checked : Checked 1703936 1712128 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1703936 128 c1703936) (checkChunk_sound 1704064 128 c1704064)) (Checked.append (checkChunk_sound 1704192 128 c1704192) (checkChunk_sound 1704320 128 c1704320))) (Checked.append (Checked.append (checkChunk_sound 1704448 128 c1704448) (checkChunk_sound 1704576 128 c1704576)) (Checked.append (checkChunk_sound 1704704 128 c1704704) (checkChunk_sound 1704832 128 c1704832)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1704960 128 c1704960) (checkChunk_sound 1705088 128 c1705088)) (Checked.append (checkChunk_sound 1705216 128 c1705216) (checkChunk_sound 1705344 128 c1705344))) (Checked.append (Checked.append (checkChunk_sound 1705472 128 c1705472) (checkChunk_sound 1705600 128 c1705600)) (Checked.append (checkChunk_sound 1705728 128 c1705728) (checkChunk_sound 1705856 128 c1705856))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1705984 128 c1705984) (checkChunk_sound 1706112 128 c1706112)) (Checked.append (checkChunk_sound 1706240 128 c1706240) (checkChunk_sound 1706368 128 c1706368))) (Checked.append (Checked.append (checkChunk_sound 1706496 128 c1706496) (checkChunk_sound 1706624 128 c1706624)) (Checked.append (checkChunk_sound 1706752 128 c1706752) (checkChunk_sound 1706880 128 c1706880)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1707008 128 c1707008) (checkChunk_sound 1707136 128 c1707136)) (Checked.append (checkChunk_sound 1707264 128 c1707264) (checkChunk_sound 1707392 128 c1707392))) (Checked.append (Checked.append (checkChunk_sound 1707520 128 c1707520) (checkChunk_sound 1707648 128 c1707648)) (Checked.append (checkChunk_sound 1707776 128 c1707776) (checkChunk_sound 1707904 128 c1707904)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1708032 128 c1708032) (checkChunk_sound 1708160 128 c1708160)) (Checked.append (checkChunk_sound 1708288 128 c1708288) (checkChunk_sound 1708416 128 c1708416))) (Checked.append (Checked.append (checkChunk_sound 1708544 128 c1708544) (checkChunk_sound 1708672 128 c1708672)) (Checked.append (checkChunk_sound 1708800 128 c1708800) (checkChunk_sound 1708928 128 c1708928)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1709056 128 c1709056) (checkChunk_sound 1709184 128 c1709184)) (Checked.append (checkChunk_sound 1709312 128 c1709312) (checkChunk_sound 1709440 128 c1709440))) (Checked.append (Checked.append (checkChunk_sound 1709568 128 c1709568) (checkChunk_sound 1709696 128 c1709696)) (Checked.append (checkChunk_sound 1709824 128 c1709824) (checkChunk_sound 1709952 128 c1709952))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1710080 128 c1710080) (checkChunk_sound 1710208 128 c1710208)) (Checked.append (checkChunk_sound 1710336 128 c1710336) (checkChunk_sound 1710464 128 c1710464))) (Checked.append (Checked.append (checkChunk_sound 1710592 128 c1710592) (checkChunk_sound 1710720 128 c1710720)) (Checked.append (checkChunk_sound 1710848 128 c1710848) (checkChunk_sound 1710976 128 c1710976)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1711104 128 c1711104) (checkChunk_sound 1711232 128 c1711232)) (Checked.append (checkChunk_sound 1711360 128 c1711360) (checkChunk_sound 1711488 128 c1711488))) (Checked.append (Checked.append (checkChunk_sound 1711616 128 c1711616) (checkChunk_sound 1711744 128 c1711744)) (Checked.append (checkChunk_sound 1711872 128 c1711872) (checkChunk_sound 1712000 128 c1712000)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B025
