module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [679936, 688128).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B004
private theorem c679936 : checkChunk 679936 128 = true := by decide +kernel
private theorem c680064 : checkChunk 680064 128 = true := by decide +kernel
private theorem c680192 : checkChunk 680192 128 = true := by decide +kernel
private theorem c680320 : checkChunk 680320 128 = true := by decide +kernel
private theorem c680448 : checkChunk 680448 128 = true := by decide +kernel
private theorem c680576 : checkChunk 680576 128 = true := by decide +kernel
private theorem c680704 : checkChunk 680704 128 = true := by decide +kernel
private theorem c680832 : checkChunk 680832 128 = true := by decide +kernel
private theorem c680960 : checkChunk 680960 128 = true := by decide +kernel
private theorem c681088 : checkChunk 681088 128 = true := by decide +kernel
private theorem c681216 : checkChunk 681216 128 = true := by decide +kernel
private theorem c681344 : checkChunk 681344 128 = true := by decide +kernel
private theorem c681472 : checkChunk 681472 128 = true := by decide +kernel
private theorem c681600 : checkChunk 681600 128 = true := by decide +kernel
private theorem c681728 : checkChunk 681728 128 = true := by decide +kernel
private theorem c681856 : checkChunk 681856 128 = true := by decide +kernel
private theorem c681984 : checkChunk 681984 128 = true := by decide +kernel
private theorem c682112 : checkChunk 682112 128 = true := by decide +kernel
private theorem c682240 : checkChunk 682240 128 = true := by decide +kernel
private theorem c682368 : checkChunk 682368 128 = true := by decide +kernel
private theorem c682496 : checkChunk 682496 128 = true := by decide +kernel
private theorem c682624 : checkChunk 682624 128 = true := by decide +kernel
private theorem c682752 : checkChunk 682752 128 = true := by decide +kernel
private theorem c682880 : checkChunk 682880 128 = true := by decide +kernel
private theorem c683008 : checkChunk 683008 128 = true := by decide +kernel
private theorem c683136 : checkChunk 683136 128 = true := by decide +kernel
private theorem c683264 : checkChunk 683264 128 = true := by decide +kernel
private theorem c683392 : checkChunk 683392 128 = true := by decide +kernel
private theorem c683520 : checkChunk 683520 128 = true := by decide +kernel
private theorem c683648 : checkChunk 683648 128 = true := by decide +kernel
private theorem c683776 : checkChunk 683776 128 = true := by decide +kernel
private theorem c683904 : checkChunk 683904 128 = true := by decide +kernel
private theorem c684032 : checkChunk 684032 128 = true := by decide +kernel
private theorem c684160 : checkChunk 684160 128 = true := by decide +kernel
private theorem c684288 : checkChunk 684288 128 = true := by decide +kernel
private theorem c684416 : checkChunk 684416 128 = true := by decide +kernel
private theorem c684544 : checkChunk 684544 128 = true := by decide +kernel
private theorem c684672 : checkChunk 684672 128 = true := by decide +kernel
private theorem c684800 : checkChunk 684800 128 = true := by decide +kernel
private theorem c684928 : checkChunk 684928 128 = true := by decide +kernel
private theorem c685056 : checkChunk 685056 128 = true := by decide +kernel
private theorem c685184 : checkChunk 685184 128 = true := by decide +kernel
private theorem c685312 : checkChunk 685312 128 = true := by decide +kernel
private theorem c685440 : checkChunk 685440 128 = true := by decide +kernel
private theorem c685568 : checkChunk 685568 128 = true := by decide +kernel
private theorem c685696 : checkChunk 685696 128 = true := by decide +kernel
private theorem c685824 : checkChunk 685824 128 = true := by decide +kernel
private theorem c685952 : checkChunk 685952 128 = true := by decide +kernel
private theorem c686080 : checkChunk 686080 128 = true := by decide +kernel
private theorem c686208 : checkChunk 686208 128 = true := by decide +kernel
private theorem c686336 : checkChunk 686336 128 = true := by decide +kernel
private theorem c686464 : checkChunk 686464 128 = true := by decide +kernel
private theorem c686592 : checkChunk 686592 128 = true := by decide +kernel
private theorem c686720 : checkChunk 686720 128 = true := by decide +kernel
private theorem c686848 : checkChunk 686848 128 = true := by decide +kernel
private theorem c686976 : checkChunk 686976 128 = true := by decide +kernel
private theorem c687104 : checkChunk 687104 128 = true := by decide +kernel
private theorem c687232 : checkChunk 687232 128 = true := by decide +kernel
private theorem c687360 : checkChunk 687360 128 = true := by decide +kernel
private theorem c687488 : checkChunk 687488 128 = true := by decide +kernel
private theorem c687616 : checkChunk 687616 128 = true := by decide +kernel
private theorem c687744 : checkChunk 687744 128 = true := by decide +kernel
private theorem c687872 : checkChunk 687872 128 = true := by decide +kernel
private theorem c688000 : checkChunk 688000 128 = true := by decide +kernel

public theorem checked : Checked 679936 688128 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 679936 128 c679936) (checkChunk_sound 680064 128 c680064)) (Checked.append (checkChunk_sound 680192 128 c680192) (checkChunk_sound 680320 128 c680320))) (Checked.append (Checked.append (checkChunk_sound 680448 128 c680448) (checkChunk_sound 680576 128 c680576)) (Checked.append (checkChunk_sound 680704 128 c680704) (checkChunk_sound 680832 128 c680832)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 680960 128 c680960) (checkChunk_sound 681088 128 c681088)) (Checked.append (checkChunk_sound 681216 128 c681216) (checkChunk_sound 681344 128 c681344))) (Checked.append (Checked.append (checkChunk_sound 681472 128 c681472) (checkChunk_sound 681600 128 c681600)) (Checked.append (checkChunk_sound 681728 128 c681728) (checkChunk_sound 681856 128 c681856))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 681984 128 c681984) (checkChunk_sound 682112 128 c682112)) (Checked.append (checkChunk_sound 682240 128 c682240) (checkChunk_sound 682368 128 c682368))) (Checked.append (Checked.append (checkChunk_sound 682496 128 c682496) (checkChunk_sound 682624 128 c682624)) (Checked.append (checkChunk_sound 682752 128 c682752) (checkChunk_sound 682880 128 c682880)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 683008 128 c683008) (checkChunk_sound 683136 128 c683136)) (Checked.append (checkChunk_sound 683264 128 c683264) (checkChunk_sound 683392 128 c683392))) (Checked.append (Checked.append (checkChunk_sound 683520 128 c683520) (checkChunk_sound 683648 128 c683648)) (Checked.append (checkChunk_sound 683776 128 c683776) (checkChunk_sound 683904 128 c683904)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 684032 128 c684032) (checkChunk_sound 684160 128 c684160)) (Checked.append (checkChunk_sound 684288 128 c684288) (checkChunk_sound 684416 128 c684416))) (Checked.append (Checked.append (checkChunk_sound 684544 128 c684544) (checkChunk_sound 684672 128 c684672)) (Checked.append (checkChunk_sound 684800 128 c684800) (checkChunk_sound 684928 128 c684928)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 685056 128 c685056) (checkChunk_sound 685184 128 c685184)) (Checked.append (checkChunk_sound 685312 128 c685312) (checkChunk_sound 685440 128 c685440))) (Checked.append (Checked.append (checkChunk_sound 685568 128 c685568) (checkChunk_sound 685696 128 c685696)) (Checked.append (checkChunk_sound 685824 128 c685824) (checkChunk_sound 685952 128 c685952))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 686080 128 c686080) (checkChunk_sound 686208 128 c686208)) (Checked.append (checkChunk_sound 686336 128 c686336) (checkChunk_sound 686464 128 c686464))) (Checked.append (Checked.append (checkChunk_sound 686592 128 c686592) (checkChunk_sound 686720 128 c686720)) (Checked.append (checkChunk_sound 686848 128 c686848) (checkChunk_sound 686976 128 c686976)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 687104 128 c687104) (checkChunk_sound 687232 128 c687232)) (Checked.append (checkChunk_sound 687360 128 c687360) (checkChunk_sound 687488 128 c687488))) (Checked.append (Checked.append (checkChunk_sound 687616 128 c687616) (checkChunk_sound 687744 128 c687744)) (Checked.append (checkChunk_sound 687872 128 c687872) (checkChunk_sound 688000 128 c688000)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B004
