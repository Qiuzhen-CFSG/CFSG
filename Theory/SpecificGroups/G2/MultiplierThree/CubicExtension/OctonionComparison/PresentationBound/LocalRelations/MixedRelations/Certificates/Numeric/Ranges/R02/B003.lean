module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [458752, 466944).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B003
private theorem c458752 : checkChunk 458752 128 = true := by decide +kernel
private theorem c458880 : checkChunk 458880 128 = true := by decide +kernel
private theorem c459008 : checkChunk 459008 128 = true := by decide +kernel
private theorem c459136 : checkChunk 459136 128 = true := by decide +kernel
private theorem c459264 : checkChunk 459264 128 = true := by decide +kernel
private theorem c459392 : checkChunk 459392 128 = true := by decide +kernel
private theorem c459520 : checkChunk 459520 128 = true := by decide +kernel
private theorem c459648 : checkChunk 459648 128 = true := by decide +kernel
private theorem c459776 : checkChunk 459776 128 = true := by decide +kernel
private theorem c459904 : checkChunk 459904 128 = true := by decide +kernel
private theorem c460032 : checkChunk 460032 128 = true := by decide +kernel
private theorem c460160 : checkChunk 460160 128 = true := by decide +kernel
private theorem c460288 : checkChunk 460288 128 = true := by decide +kernel
private theorem c460416 : checkChunk 460416 128 = true := by decide +kernel
private theorem c460544 : checkChunk 460544 128 = true := by decide +kernel
private theorem c460672 : checkChunk 460672 128 = true := by decide +kernel
private theorem c460800 : checkChunk 460800 128 = true := by decide +kernel
private theorem c460928 : checkChunk 460928 128 = true := by decide +kernel
private theorem c461056 : checkChunk 461056 128 = true := by decide +kernel
private theorem c461184 : checkChunk 461184 128 = true := by decide +kernel
private theorem c461312 : checkChunk 461312 128 = true := by decide +kernel
private theorem c461440 : checkChunk 461440 128 = true := by decide +kernel
private theorem c461568 : checkChunk 461568 128 = true := by decide +kernel
private theorem c461696 : checkChunk 461696 128 = true := by decide +kernel
private theorem c461824 : checkChunk 461824 128 = true := by decide +kernel
private theorem c461952 : checkChunk 461952 128 = true := by decide +kernel
private theorem c462080 : checkChunk 462080 128 = true := by decide +kernel
private theorem c462208 : checkChunk 462208 128 = true := by decide +kernel
private theorem c462336 : checkChunk 462336 128 = true := by decide +kernel
private theorem c462464 : checkChunk 462464 128 = true := by decide +kernel
private theorem c462592 : checkChunk 462592 128 = true := by decide +kernel
private theorem c462720 : checkChunk 462720 128 = true := by decide +kernel
private theorem c462848 : checkChunk 462848 128 = true := by decide +kernel
private theorem c462976 : checkChunk 462976 128 = true := by decide +kernel
private theorem c463104 : checkChunk 463104 128 = true := by decide +kernel
private theorem c463232 : checkChunk 463232 128 = true := by decide +kernel
private theorem c463360 : checkChunk 463360 128 = true := by decide +kernel
private theorem c463488 : checkChunk 463488 128 = true := by decide +kernel
private theorem c463616 : checkChunk 463616 128 = true := by decide +kernel
private theorem c463744 : checkChunk 463744 128 = true := by decide +kernel
private theorem c463872 : checkChunk 463872 128 = true := by decide +kernel
private theorem c464000 : checkChunk 464000 128 = true := by decide +kernel
private theorem c464128 : checkChunk 464128 128 = true := by decide +kernel
private theorem c464256 : checkChunk 464256 128 = true := by decide +kernel
private theorem c464384 : checkChunk 464384 128 = true := by decide +kernel
private theorem c464512 : checkChunk 464512 128 = true := by decide +kernel
private theorem c464640 : checkChunk 464640 128 = true := by decide +kernel
private theorem c464768 : checkChunk 464768 128 = true := by decide +kernel
private theorem c464896 : checkChunk 464896 128 = true := by decide +kernel
private theorem c465024 : checkChunk 465024 128 = true := by decide +kernel
private theorem c465152 : checkChunk 465152 128 = true := by decide +kernel
private theorem c465280 : checkChunk 465280 128 = true := by decide +kernel
private theorem c465408 : checkChunk 465408 128 = true := by decide +kernel
private theorem c465536 : checkChunk 465536 128 = true := by decide +kernel
private theorem c465664 : checkChunk 465664 128 = true := by decide +kernel
private theorem c465792 : checkChunk 465792 128 = true := by decide +kernel
private theorem c465920 : checkChunk 465920 128 = true := by decide +kernel
private theorem c466048 : checkChunk 466048 128 = true := by decide +kernel
private theorem c466176 : checkChunk 466176 128 = true := by decide +kernel
private theorem c466304 : checkChunk 466304 128 = true := by decide +kernel
private theorem c466432 : checkChunk 466432 128 = true := by decide +kernel
private theorem c466560 : checkChunk 466560 128 = true := by decide +kernel
private theorem c466688 : checkChunk 466688 128 = true := by decide +kernel
private theorem c466816 : checkChunk 466816 128 = true := by decide +kernel

public theorem checked : Checked 458752 466944 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 458752 128 c458752) (checkChunk_sound 458880 128 c458880)) (Checked.append (checkChunk_sound 459008 128 c459008) (checkChunk_sound 459136 128 c459136))) (Checked.append (Checked.append (checkChunk_sound 459264 128 c459264) (checkChunk_sound 459392 128 c459392)) (Checked.append (checkChunk_sound 459520 128 c459520) (checkChunk_sound 459648 128 c459648)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 459776 128 c459776) (checkChunk_sound 459904 128 c459904)) (Checked.append (checkChunk_sound 460032 128 c460032) (checkChunk_sound 460160 128 c460160))) (Checked.append (Checked.append (checkChunk_sound 460288 128 c460288) (checkChunk_sound 460416 128 c460416)) (Checked.append (checkChunk_sound 460544 128 c460544) (checkChunk_sound 460672 128 c460672))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 460800 128 c460800) (checkChunk_sound 460928 128 c460928)) (Checked.append (checkChunk_sound 461056 128 c461056) (checkChunk_sound 461184 128 c461184))) (Checked.append (Checked.append (checkChunk_sound 461312 128 c461312) (checkChunk_sound 461440 128 c461440)) (Checked.append (checkChunk_sound 461568 128 c461568) (checkChunk_sound 461696 128 c461696)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 461824 128 c461824) (checkChunk_sound 461952 128 c461952)) (Checked.append (checkChunk_sound 462080 128 c462080) (checkChunk_sound 462208 128 c462208))) (Checked.append (Checked.append (checkChunk_sound 462336 128 c462336) (checkChunk_sound 462464 128 c462464)) (Checked.append (checkChunk_sound 462592 128 c462592) (checkChunk_sound 462720 128 c462720)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 462848 128 c462848) (checkChunk_sound 462976 128 c462976)) (Checked.append (checkChunk_sound 463104 128 c463104) (checkChunk_sound 463232 128 c463232))) (Checked.append (Checked.append (checkChunk_sound 463360 128 c463360) (checkChunk_sound 463488 128 c463488)) (Checked.append (checkChunk_sound 463616 128 c463616) (checkChunk_sound 463744 128 c463744)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 463872 128 c463872) (checkChunk_sound 464000 128 c464000)) (Checked.append (checkChunk_sound 464128 128 c464128) (checkChunk_sound 464256 128 c464256))) (Checked.append (Checked.append (checkChunk_sound 464384 128 c464384) (checkChunk_sound 464512 128 c464512)) (Checked.append (checkChunk_sound 464640 128 c464640) (checkChunk_sound 464768 128 c464768))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 464896 128 c464896) (checkChunk_sound 465024 128 c465024)) (Checked.append (checkChunk_sound 465152 128 c465152) (checkChunk_sound 465280 128 c465280))) (Checked.append (Checked.append (checkChunk_sound 465408 128 c465408) (checkChunk_sound 465536 128 c465536)) (Checked.append (checkChunk_sound 465664 128 c465664) (checkChunk_sound 465792 128 c465792)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 465920 128 c465920) (checkChunk_sound 466048 128 c466048)) (Checked.append (checkChunk_sound 466176 128 c466176) (checkChunk_sound 466304 128 c466304))) (Checked.append (Checked.append (checkChunk_sound 466432 128 c466432) (checkChunk_sound 466560 128 c466560)) (Checked.append (checkChunk_sound 466688 128 c466688) (checkChunk_sound 466816 128 c466816)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B003
