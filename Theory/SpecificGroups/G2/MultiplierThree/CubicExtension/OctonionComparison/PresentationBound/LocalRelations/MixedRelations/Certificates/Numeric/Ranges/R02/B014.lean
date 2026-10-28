module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [548864, 557056).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B014
private theorem c548864 : checkChunk 548864 128 = true := by decide +kernel
private theorem c548992 : checkChunk 548992 128 = true := by decide +kernel
private theorem c549120 : checkChunk 549120 128 = true := by decide +kernel
private theorem c549248 : checkChunk 549248 128 = true := by decide +kernel
private theorem c549376 : checkChunk 549376 128 = true := by decide +kernel
private theorem c549504 : checkChunk 549504 128 = true := by decide +kernel
private theorem c549632 : checkChunk 549632 128 = true := by decide +kernel
private theorem c549760 : checkChunk 549760 128 = true := by decide +kernel
private theorem c549888 : checkChunk 549888 128 = true := by decide +kernel
private theorem c550016 : checkChunk 550016 128 = true := by decide +kernel
private theorem c550144 : checkChunk 550144 128 = true := by decide +kernel
private theorem c550272 : checkChunk 550272 128 = true := by decide +kernel
private theorem c550400 : checkChunk 550400 128 = true := by decide +kernel
private theorem c550528 : checkChunk 550528 128 = true := by decide +kernel
private theorem c550656 : checkChunk 550656 128 = true := by decide +kernel
private theorem c550784 : checkChunk 550784 128 = true := by decide +kernel
private theorem c550912 : checkChunk 550912 128 = true := by decide +kernel
private theorem c551040 : checkChunk 551040 128 = true := by decide +kernel
private theorem c551168 : checkChunk 551168 128 = true := by decide +kernel
private theorem c551296 : checkChunk 551296 128 = true := by decide +kernel
private theorem c551424 : checkChunk 551424 128 = true := by decide +kernel
private theorem c551552 : checkChunk 551552 128 = true := by decide +kernel
private theorem c551680 : checkChunk 551680 128 = true := by decide +kernel
private theorem c551808 : checkChunk 551808 128 = true := by decide +kernel
private theorem c551936 : checkChunk 551936 128 = true := by decide +kernel
private theorem c552064 : checkChunk 552064 128 = true := by decide +kernel
private theorem c552192 : checkChunk 552192 128 = true := by decide +kernel
private theorem c552320 : checkChunk 552320 128 = true := by decide +kernel
private theorem c552448 : checkChunk 552448 128 = true := by decide +kernel
private theorem c552576 : checkChunk 552576 128 = true := by decide +kernel
private theorem c552704 : checkChunk 552704 128 = true := by decide +kernel
private theorem c552832 : checkChunk 552832 128 = true := by decide +kernel
private theorem c552960 : checkChunk 552960 128 = true := by decide +kernel
private theorem c553088 : checkChunk 553088 128 = true := by decide +kernel
private theorem c553216 : checkChunk 553216 128 = true := by decide +kernel
private theorem c553344 : checkChunk 553344 128 = true := by decide +kernel
private theorem c553472 : checkChunk 553472 128 = true := by decide +kernel
private theorem c553600 : checkChunk 553600 128 = true := by decide +kernel
private theorem c553728 : checkChunk 553728 128 = true := by decide +kernel
private theorem c553856 : checkChunk 553856 128 = true := by decide +kernel
private theorem c553984 : checkChunk 553984 128 = true := by decide +kernel
private theorem c554112 : checkChunk 554112 128 = true := by decide +kernel
private theorem c554240 : checkChunk 554240 128 = true := by decide +kernel
private theorem c554368 : checkChunk 554368 128 = true := by decide +kernel
private theorem c554496 : checkChunk 554496 128 = true := by decide +kernel
private theorem c554624 : checkChunk 554624 128 = true := by decide +kernel
private theorem c554752 : checkChunk 554752 128 = true := by decide +kernel
private theorem c554880 : checkChunk 554880 128 = true := by decide +kernel
private theorem c555008 : checkChunk 555008 128 = true := by decide +kernel
private theorem c555136 : checkChunk 555136 128 = true := by decide +kernel
private theorem c555264 : checkChunk 555264 128 = true := by decide +kernel
private theorem c555392 : checkChunk 555392 128 = true := by decide +kernel
private theorem c555520 : checkChunk 555520 128 = true := by decide +kernel
private theorem c555648 : checkChunk 555648 128 = true := by decide +kernel
private theorem c555776 : checkChunk 555776 128 = true := by decide +kernel
private theorem c555904 : checkChunk 555904 128 = true := by decide +kernel
private theorem c556032 : checkChunk 556032 128 = true := by decide +kernel
private theorem c556160 : checkChunk 556160 128 = true := by decide +kernel
private theorem c556288 : checkChunk 556288 128 = true := by decide +kernel
private theorem c556416 : checkChunk 556416 128 = true := by decide +kernel
private theorem c556544 : checkChunk 556544 128 = true := by decide +kernel
private theorem c556672 : checkChunk 556672 128 = true := by decide +kernel
private theorem c556800 : checkChunk 556800 128 = true := by decide +kernel
private theorem c556928 : checkChunk 556928 128 = true := by decide +kernel

public theorem checked : Checked 548864 557056 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 548864 128 c548864) (checkChunk_sound 548992 128 c548992)) (Checked.append (checkChunk_sound 549120 128 c549120) (checkChunk_sound 549248 128 c549248))) (Checked.append (Checked.append (checkChunk_sound 549376 128 c549376) (checkChunk_sound 549504 128 c549504)) (Checked.append (checkChunk_sound 549632 128 c549632) (checkChunk_sound 549760 128 c549760)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 549888 128 c549888) (checkChunk_sound 550016 128 c550016)) (Checked.append (checkChunk_sound 550144 128 c550144) (checkChunk_sound 550272 128 c550272))) (Checked.append (Checked.append (checkChunk_sound 550400 128 c550400) (checkChunk_sound 550528 128 c550528)) (Checked.append (checkChunk_sound 550656 128 c550656) (checkChunk_sound 550784 128 c550784))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 550912 128 c550912) (checkChunk_sound 551040 128 c551040)) (Checked.append (checkChunk_sound 551168 128 c551168) (checkChunk_sound 551296 128 c551296))) (Checked.append (Checked.append (checkChunk_sound 551424 128 c551424) (checkChunk_sound 551552 128 c551552)) (Checked.append (checkChunk_sound 551680 128 c551680) (checkChunk_sound 551808 128 c551808)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 551936 128 c551936) (checkChunk_sound 552064 128 c552064)) (Checked.append (checkChunk_sound 552192 128 c552192) (checkChunk_sound 552320 128 c552320))) (Checked.append (Checked.append (checkChunk_sound 552448 128 c552448) (checkChunk_sound 552576 128 c552576)) (Checked.append (checkChunk_sound 552704 128 c552704) (checkChunk_sound 552832 128 c552832)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 552960 128 c552960) (checkChunk_sound 553088 128 c553088)) (Checked.append (checkChunk_sound 553216 128 c553216) (checkChunk_sound 553344 128 c553344))) (Checked.append (Checked.append (checkChunk_sound 553472 128 c553472) (checkChunk_sound 553600 128 c553600)) (Checked.append (checkChunk_sound 553728 128 c553728) (checkChunk_sound 553856 128 c553856)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 553984 128 c553984) (checkChunk_sound 554112 128 c554112)) (Checked.append (checkChunk_sound 554240 128 c554240) (checkChunk_sound 554368 128 c554368))) (Checked.append (Checked.append (checkChunk_sound 554496 128 c554496) (checkChunk_sound 554624 128 c554624)) (Checked.append (checkChunk_sound 554752 128 c554752) (checkChunk_sound 554880 128 c554880))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 555008 128 c555008) (checkChunk_sound 555136 128 c555136)) (Checked.append (checkChunk_sound 555264 128 c555264) (checkChunk_sound 555392 128 c555392))) (Checked.append (Checked.append (checkChunk_sound 555520 128 c555520) (checkChunk_sound 555648 128 c555648)) (Checked.append (checkChunk_sound 555776 128 c555776) (checkChunk_sound 555904 128 c555904)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 556032 128 c556032) (checkChunk_sound 556160 128 c556160)) (Checked.append (checkChunk_sound 556288 128 c556288) (checkChunk_sound 556416 128 c556416))) (Checked.append (Checked.append (checkChunk_sound 556544 128 c556544) (checkChunk_sound 556672 128 c556672)) (Checked.append (checkChunk_sound 556800 128 c556800) (checkChunk_sound 556928 128 c556928)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02.B014
