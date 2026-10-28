module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [811008, 819200).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B020
private theorem c811008 : checkChunk 811008 128 = true := by decide +kernel
private theorem c811136 : checkChunk 811136 128 = true := by decide +kernel
private theorem c811264 : checkChunk 811264 128 = true := by decide +kernel
private theorem c811392 : checkChunk 811392 128 = true := by decide +kernel
private theorem c811520 : checkChunk 811520 128 = true := by decide +kernel
private theorem c811648 : checkChunk 811648 128 = true := by decide +kernel
private theorem c811776 : checkChunk 811776 128 = true := by decide +kernel
private theorem c811904 : checkChunk 811904 128 = true := by decide +kernel
private theorem c812032 : checkChunk 812032 128 = true := by decide +kernel
private theorem c812160 : checkChunk 812160 128 = true := by decide +kernel
private theorem c812288 : checkChunk 812288 128 = true := by decide +kernel
private theorem c812416 : checkChunk 812416 128 = true := by decide +kernel
private theorem c812544 : checkChunk 812544 128 = true := by decide +kernel
private theorem c812672 : checkChunk 812672 128 = true := by decide +kernel
private theorem c812800 : checkChunk 812800 128 = true := by decide +kernel
private theorem c812928 : checkChunk 812928 128 = true := by decide +kernel
private theorem c813056 : checkChunk 813056 128 = true := by decide +kernel
private theorem c813184 : checkChunk 813184 128 = true := by decide +kernel
private theorem c813312 : checkChunk 813312 128 = true := by decide +kernel
private theorem c813440 : checkChunk 813440 128 = true := by decide +kernel
private theorem c813568 : checkChunk 813568 128 = true := by decide +kernel
private theorem c813696 : checkChunk 813696 128 = true := by decide +kernel
private theorem c813824 : checkChunk 813824 128 = true := by decide +kernel
private theorem c813952 : checkChunk 813952 128 = true := by decide +kernel
private theorem c814080 : checkChunk 814080 128 = true := by decide +kernel
private theorem c814208 : checkChunk 814208 128 = true := by decide +kernel
private theorem c814336 : checkChunk 814336 128 = true := by decide +kernel
private theorem c814464 : checkChunk 814464 128 = true := by decide +kernel
private theorem c814592 : checkChunk 814592 128 = true := by decide +kernel
private theorem c814720 : checkChunk 814720 128 = true := by decide +kernel
private theorem c814848 : checkChunk 814848 128 = true := by decide +kernel
private theorem c814976 : checkChunk 814976 128 = true := by decide +kernel
private theorem c815104 : checkChunk 815104 128 = true := by decide +kernel
private theorem c815232 : checkChunk 815232 128 = true := by decide +kernel
private theorem c815360 : checkChunk 815360 128 = true := by decide +kernel
private theorem c815488 : checkChunk 815488 128 = true := by decide +kernel
private theorem c815616 : checkChunk 815616 128 = true := by decide +kernel
private theorem c815744 : checkChunk 815744 128 = true := by decide +kernel
private theorem c815872 : checkChunk 815872 128 = true := by decide +kernel
private theorem c816000 : checkChunk 816000 128 = true := by decide +kernel
private theorem c816128 : checkChunk 816128 128 = true := by decide +kernel
private theorem c816256 : checkChunk 816256 128 = true := by decide +kernel
private theorem c816384 : checkChunk 816384 128 = true := by decide +kernel
private theorem c816512 : checkChunk 816512 128 = true := by decide +kernel
private theorem c816640 : checkChunk 816640 128 = true := by decide +kernel
private theorem c816768 : checkChunk 816768 128 = true := by decide +kernel
private theorem c816896 : checkChunk 816896 128 = true := by decide +kernel
private theorem c817024 : checkChunk 817024 128 = true := by decide +kernel
private theorem c817152 : checkChunk 817152 128 = true := by decide +kernel
private theorem c817280 : checkChunk 817280 128 = true := by decide +kernel
private theorem c817408 : checkChunk 817408 128 = true := by decide +kernel
private theorem c817536 : checkChunk 817536 128 = true := by decide +kernel
private theorem c817664 : checkChunk 817664 128 = true := by decide +kernel
private theorem c817792 : checkChunk 817792 128 = true := by decide +kernel
private theorem c817920 : checkChunk 817920 128 = true := by decide +kernel
private theorem c818048 : checkChunk 818048 128 = true := by decide +kernel
private theorem c818176 : checkChunk 818176 128 = true := by decide +kernel
private theorem c818304 : checkChunk 818304 128 = true := by decide +kernel
private theorem c818432 : checkChunk 818432 128 = true := by decide +kernel
private theorem c818560 : checkChunk 818560 128 = true := by decide +kernel
private theorem c818688 : checkChunk 818688 128 = true := by decide +kernel
private theorem c818816 : checkChunk 818816 128 = true := by decide +kernel
private theorem c818944 : checkChunk 818944 128 = true := by decide +kernel
private theorem c819072 : checkChunk 819072 128 = true := by decide +kernel

public theorem checked : Checked 811008 819200 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 811008 128 c811008) (checkChunk_sound 811136 128 c811136)) (Checked.append (checkChunk_sound 811264 128 c811264) (checkChunk_sound 811392 128 c811392))) (Checked.append (Checked.append (checkChunk_sound 811520 128 c811520) (checkChunk_sound 811648 128 c811648)) (Checked.append (checkChunk_sound 811776 128 c811776) (checkChunk_sound 811904 128 c811904)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 812032 128 c812032) (checkChunk_sound 812160 128 c812160)) (Checked.append (checkChunk_sound 812288 128 c812288) (checkChunk_sound 812416 128 c812416))) (Checked.append (Checked.append (checkChunk_sound 812544 128 c812544) (checkChunk_sound 812672 128 c812672)) (Checked.append (checkChunk_sound 812800 128 c812800) (checkChunk_sound 812928 128 c812928))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 813056 128 c813056) (checkChunk_sound 813184 128 c813184)) (Checked.append (checkChunk_sound 813312 128 c813312) (checkChunk_sound 813440 128 c813440))) (Checked.append (Checked.append (checkChunk_sound 813568 128 c813568) (checkChunk_sound 813696 128 c813696)) (Checked.append (checkChunk_sound 813824 128 c813824) (checkChunk_sound 813952 128 c813952)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 814080 128 c814080) (checkChunk_sound 814208 128 c814208)) (Checked.append (checkChunk_sound 814336 128 c814336) (checkChunk_sound 814464 128 c814464))) (Checked.append (Checked.append (checkChunk_sound 814592 128 c814592) (checkChunk_sound 814720 128 c814720)) (Checked.append (checkChunk_sound 814848 128 c814848) (checkChunk_sound 814976 128 c814976)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 815104 128 c815104) (checkChunk_sound 815232 128 c815232)) (Checked.append (checkChunk_sound 815360 128 c815360) (checkChunk_sound 815488 128 c815488))) (Checked.append (Checked.append (checkChunk_sound 815616 128 c815616) (checkChunk_sound 815744 128 c815744)) (Checked.append (checkChunk_sound 815872 128 c815872) (checkChunk_sound 816000 128 c816000)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 816128 128 c816128) (checkChunk_sound 816256 128 c816256)) (Checked.append (checkChunk_sound 816384 128 c816384) (checkChunk_sound 816512 128 c816512))) (Checked.append (Checked.append (checkChunk_sound 816640 128 c816640) (checkChunk_sound 816768 128 c816768)) (Checked.append (checkChunk_sound 816896 128 c816896) (checkChunk_sound 817024 128 c817024))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 817152 128 c817152) (checkChunk_sound 817280 128 c817280)) (Checked.append (checkChunk_sound 817408 128 c817408) (checkChunk_sound 817536 128 c817536))) (Checked.append (Checked.append (checkChunk_sound 817664 128 c817664) (checkChunk_sound 817792 128 c817792)) (Checked.append (checkChunk_sound 817920 128 c817920) (checkChunk_sound 818048 128 c818048)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 818176 128 c818176) (checkChunk_sound 818304 128 c818304)) (Checked.append (checkChunk_sound 818432 128 c818432) (checkChunk_sound 818560 128 c818560))) (Checked.append (Checked.append (checkChunk_sound 818688 128 c818688) (checkChunk_sound 818816 128 c818816)) (Checked.append (checkChunk_sound 818944 128 c818944) (checkChunk_sound 819072 128 c819072)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B020
