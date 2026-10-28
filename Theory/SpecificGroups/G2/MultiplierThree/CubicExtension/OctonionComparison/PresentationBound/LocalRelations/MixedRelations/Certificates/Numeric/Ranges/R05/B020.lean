module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1236992, 1245184).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B020
private theorem c1236992 : checkChunk 1236992 128 = true := by decide +kernel
private theorem c1237120 : checkChunk 1237120 128 = true := by decide +kernel
private theorem c1237248 : checkChunk 1237248 128 = true := by decide +kernel
private theorem c1237376 : checkChunk 1237376 128 = true := by decide +kernel
private theorem c1237504 : checkChunk 1237504 128 = true := by decide +kernel
private theorem c1237632 : checkChunk 1237632 128 = true := by decide +kernel
private theorem c1237760 : checkChunk 1237760 128 = true := by decide +kernel
private theorem c1237888 : checkChunk 1237888 128 = true := by decide +kernel
private theorem c1238016 : checkChunk 1238016 128 = true := by decide +kernel
private theorem c1238144 : checkChunk 1238144 128 = true := by decide +kernel
private theorem c1238272 : checkChunk 1238272 128 = true := by decide +kernel
private theorem c1238400 : checkChunk 1238400 128 = true := by decide +kernel
private theorem c1238528 : checkChunk 1238528 128 = true := by decide +kernel
private theorem c1238656 : checkChunk 1238656 128 = true := by decide +kernel
private theorem c1238784 : checkChunk 1238784 128 = true := by decide +kernel
private theorem c1238912 : checkChunk 1238912 128 = true := by decide +kernel
private theorem c1239040 : checkChunk 1239040 128 = true := by decide +kernel
private theorem c1239168 : checkChunk 1239168 128 = true := by decide +kernel
private theorem c1239296 : checkChunk 1239296 128 = true := by decide +kernel
private theorem c1239424 : checkChunk 1239424 128 = true := by decide +kernel
private theorem c1239552 : checkChunk 1239552 128 = true := by decide +kernel
private theorem c1239680 : checkChunk 1239680 128 = true := by decide +kernel
private theorem c1239808 : checkChunk 1239808 128 = true := by decide +kernel
private theorem c1239936 : checkChunk 1239936 128 = true := by decide +kernel
private theorem c1240064 : checkChunk 1240064 128 = true := by decide +kernel
private theorem c1240192 : checkChunk 1240192 128 = true := by decide +kernel
private theorem c1240320 : checkChunk 1240320 128 = true := by decide +kernel
private theorem c1240448 : checkChunk 1240448 128 = true := by decide +kernel
private theorem c1240576 : checkChunk 1240576 128 = true := by decide +kernel
private theorem c1240704 : checkChunk 1240704 128 = true := by decide +kernel
private theorem c1240832 : checkChunk 1240832 128 = true := by decide +kernel
private theorem c1240960 : checkChunk 1240960 128 = true := by decide +kernel
private theorem c1241088 : checkChunk 1241088 128 = true := by decide +kernel
private theorem c1241216 : checkChunk 1241216 128 = true := by decide +kernel
private theorem c1241344 : checkChunk 1241344 128 = true := by decide +kernel
private theorem c1241472 : checkChunk 1241472 128 = true := by decide +kernel
private theorem c1241600 : checkChunk 1241600 128 = true := by decide +kernel
private theorem c1241728 : checkChunk 1241728 128 = true := by decide +kernel
private theorem c1241856 : checkChunk 1241856 128 = true := by decide +kernel
private theorem c1241984 : checkChunk 1241984 128 = true := by decide +kernel
private theorem c1242112 : checkChunk 1242112 128 = true := by decide +kernel
private theorem c1242240 : checkChunk 1242240 128 = true := by decide +kernel
private theorem c1242368 : checkChunk 1242368 128 = true := by decide +kernel
private theorem c1242496 : checkChunk 1242496 128 = true := by decide +kernel
private theorem c1242624 : checkChunk 1242624 128 = true := by decide +kernel
private theorem c1242752 : checkChunk 1242752 128 = true := by decide +kernel
private theorem c1242880 : checkChunk 1242880 128 = true := by decide +kernel
private theorem c1243008 : checkChunk 1243008 128 = true := by decide +kernel
private theorem c1243136 : checkChunk 1243136 128 = true := by decide +kernel
private theorem c1243264 : checkChunk 1243264 128 = true := by decide +kernel
private theorem c1243392 : checkChunk 1243392 128 = true := by decide +kernel
private theorem c1243520 : checkChunk 1243520 128 = true := by decide +kernel
private theorem c1243648 : checkChunk 1243648 128 = true := by decide +kernel
private theorem c1243776 : checkChunk 1243776 128 = true := by decide +kernel
private theorem c1243904 : checkChunk 1243904 128 = true := by decide +kernel
private theorem c1244032 : checkChunk 1244032 128 = true := by decide +kernel
private theorem c1244160 : checkChunk 1244160 128 = true := by decide +kernel
private theorem c1244288 : checkChunk 1244288 128 = true := by decide +kernel
private theorem c1244416 : checkChunk 1244416 128 = true := by decide +kernel
private theorem c1244544 : checkChunk 1244544 128 = true := by decide +kernel
private theorem c1244672 : checkChunk 1244672 128 = true := by decide +kernel
private theorem c1244800 : checkChunk 1244800 128 = true := by decide +kernel
private theorem c1244928 : checkChunk 1244928 128 = true := by decide +kernel
private theorem c1245056 : checkChunk 1245056 128 = true := by decide +kernel

public theorem checked : Checked 1236992 1245184 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1236992 128 c1236992) (checkChunk_sound 1237120 128 c1237120)) (Checked.append (checkChunk_sound 1237248 128 c1237248) (checkChunk_sound 1237376 128 c1237376))) (Checked.append (Checked.append (checkChunk_sound 1237504 128 c1237504) (checkChunk_sound 1237632 128 c1237632)) (Checked.append (checkChunk_sound 1237760 128 c1237760) (checkChunk_sound 1237888 128 c1237888)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1238016 128 c1238016) (checkChunk_sound 1238144 128 c1238144)) (Checked.append (checkChunk_sound 1238272 128 c1238272) (checkChunk_sound 1238400 128 c1238400))) (Checked.append (Checked.append (checkChunk_sound 1238528 128 c1238528) (checkChunk_sound 1238656 128 c1238656)) (Checked.append (checkChunk_sound 1238784 128 c1238784) (checkChunk_sound 1238912 128 c1238912))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1239040 128 c1239040) (checkChunk_sound 1239168 128 c1239168)) (Checked.append (checkChunk_sound 1239296 128 c1239296) (checkChunk_sound 1239424 128 c1239424))) (Checked.append (Checked.append (checkChunk_sound 1239552 128 c1239552) (checkChunk_sound 1239680 128 c1239680)) (Checked.append (checkChunk_sound 1239808 128 c1239808) (checkChunk_sound 1239936 128 c1239936)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1240064 128 c1240064) (checkChunk_sound 1240192 128 c1240192)) (Checked.append (checkChunk_sound 1240320 128 c1240320) (checkChunk_sound 1240448 128 c1240448))) (Checked.append (Checked.append (checkChunk_sound 1240576 128 c1240576) (checkChunk_sound 1240704 128 c1240704)) (Checked.append (checkChunk_sound 1240832 128 c1240832) (checkChunk_sound 1240960 128 c1240960)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1241088 128 c1241088) (checkChunk_sound 1241216 128 c1241216)) (Checked.append (checkChunk_sound 1241344 128 c1241344) (checkChunk_sound 1241472 128 c1241472))) (Checked.append (Checked.append (checkChunk_sound 1241600 128 c1241600) (checkChunk_sound 1241728 128 c1241728)) (Checked.append (checkChunk_sound 1241856 128 c1241856) (checkChunk_sound 1241984 128 c1241984)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1242112 128 c1242112) (checkChunk_sound 1242240 128 c1242240)) (Checked.append (checkChunk_sound 1242368 128 c1242368) (checkChunk_sound 1242496 128 c1242496))) (Checked.append (Checked.append (checkChunk_sound 1242624 128 c1242624) (checkChunk_sound 1242752 128 c1242752)) (Checked.append (checkChunk_sound 1242880 128 c1242880) (checkChunk_sound 1243008 128 c1243008))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1243136 128 c1243136) (checkChunk_sound 1243264 128 c1243264)) (Checked.append (checkChunk_sound 1243392 128 c1243392) (checkChunk_sound 1243520 128 c1243520))) (Checked.append (Checked.append (checkChunk_sound 1243648 128 c1243648) (checkChunk_sound 1243776 128 c1243776)) (Checked.append (checkChunk_sound 1243904 128 c1243904) (checkChunk_sound 1244032 128 c1244032)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1244160 128 c1244160) (checkChunk_sound 1244288 128 c1244288)) (Checked.append (checkChunk_sound 1244416 128 c1244416) (checkChunk_sound 1244544 128 c1244544))) (Checked.append (Checked.append (checkChunk_sound 1244672 128 c1244672) (checkChunk_sound 1244800 128 c1244800)) (Checked.append (checkChunk_sound 1244928 128 c1244928) (checkChunk_sound 1245056 128 c1245056)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B020
