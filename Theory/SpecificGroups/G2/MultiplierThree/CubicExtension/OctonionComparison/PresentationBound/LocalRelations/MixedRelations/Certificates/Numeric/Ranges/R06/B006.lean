module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1335296, 1343488).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B006
private theorem c1335296 : checkChunk 1335296 128 = true := by decide +kernel
private theorem c1335424 : checkChunk 1335424 128 = true := by decide +kernel
private theorem c1335552 : checkChunk 1335552 128 = true := by decide +kernel
private theorem c1335680 : checkChunk 1335680 128 = true := by decide +kernel
private theorem c1335808 : checkChunk 1335808 128 = true := by decide +kernel
private theorem c1335936 : checkChunk 1335936 128 = true := by decide +kernel
private theorem c1336064 : checkChunk 1336064 128 = true := by decide +kernel
private theorem c1336192 : checkChunk 1336192 128 = true := by decide +kernel
private theorem c1336320 : checkChunk 1336320 128 = true := by decide +kernel
private theorem c1336448 : checkChunk 1336448 128 = true := by decide +kernel
private theorem c1336576 : checkChunk 1336576 128 = true := by decide +kernel
private theorem c1336704 : checkChunk 1336704 128 = true := by decide +kernel
private theorem c1336832 : checkChunk 1336832 128 = true := by decide +kernel
private theorem c1336960 : checkChunk 1336960 128 = true := by decide +kernel
private theorem c1337088 : checkChunk 1337088 128 = true := by decide +kernel
private theorem c1337216 : checkChunk 1337216 128 = true := by decide +kernel
private theorem c1337344 : checkChunk 1337344 128 = true := by decide +kernel
private theorem c1337472 : checkChunk 1337472 128 = true := by decide +kernel
private theorem c1337600 : checkChunk 1337600 128 = true := by decide +kernel
private theorem c1337728 : checkChunk 1337728 128 = true := by decide +kernel
private theorem c1337856 : checkChunk 1337856 128 = true := by decide +kernel
private theorem c1337984 : checkChunk 1337984 128 = true := by decide +kernel
private theorem c1338112 : checkChunk 1338112 128 = true := by decide +kernel
private theorem c1338240 : checkChunk 1338240 128 = true := by decide +kernel
private theorem c1338368 : checkChunk 1338368 128 = true := by decide +kernel
private theorem c1338496 : checkChunk 1338496 128 = true := by decide +kernel
private theorem c1338624 : checkChunk 1338624 128 = true := by decide +kernel
private theorem c1338752 : checkChunk 1338752 128 = true := by decide +kernel
private theorem c1338880 : checkChunk 1338880 128 = true := by decide +kernel
private theorem c1339008 : checkChunk 1339008 128 = true := by decide +kernel
private theorem c1339136 : checkChunk 1339136 128 = true := by decide +kernel
private theorem c1339264 : checkChunk 1339264 128 = true := by decide +kernel
private theorem c1339392 : checkChunk 1339392 128 = true := by decide +kernel
private theorem c1339520 : checkChunk 1339520 128 = true := by decide +kernel
private theorem c1339648 : checkChunk 1339648 128 = true := by decide +kernel
private theorem c1339776 : checkChunk 1339776 128 = true := by decide +kernel
private theorem c1339904 : checkChunk 1339904 128 = true := by decide +kernel
private theorem c1340032 : checkChunk 1340032 128 = true := by decide +kernel
private theorem c1340160 : checkChunk 1340160 128 = true := by decide +kernel
private theorem c1340288 : checkChunk 1340288 128 = true := by decide +kernel
private theorem c1340416 : checkChunk 1340416 128 = true := by decide +kernel
private theorem c1340544 : checkChunk 1340544 128 = true := by decide +kernel
private theorem c1340672 : checkChunk 1340672 128 = true := by decide +kernel
private theorem c1340800 : checkChunk 1340800 128 = true := by decide +kernel
private theorem c1340928 : checkChunk 1340928 128 = true := by decide +kernel
private theorem c1341056 : checkChunk 1341056 128 = true := by decide +kernel
private theorem c1341184 : checkChunk 1341184 128 = true := by decide +kernel
private theorem c1341312 : checkChunk 1341312 128 = true := by decide +kernel
private theorem c1341440 : checkChunk 1341440 128 = true := by decide +kernel
private theorem c1341568 : checkChunk 1341568 128 = true := by decide +kernel
private theorem c1341696 : checkChunk 1341696 128 = true := by decide +kernel
private theorem c1341824 : checkChunk 1341824 128 = true := by decide +kernel
private theorem c1341952 : checkChunk 1341952 128 = true := by decide +kernel
private theorem c1342080 : checkChunk 1342080 128 = true := by decide +kernel
private theorem c1342208 : checkChunk 1342208 128 = true := by decide +kernel
private theorem c1342336 : checkChunk 1342336 128 = true := by decide +kernel
private theorem c1342464 : checkChunk 1342464 128 = true := by decide +kernel
private theorem c1342592 : checkChunk 1342592 128 = true := by decide +kernel
private theorem c1342720 : checkChunk 1342720 128 = true := by decide +kernel
private theorem c1342848 : checkChunk 1342848 128 = true := by decide +kernel
private theorem c1342976 : checkChunk 1342976 128 = true := by decide +kernel
private theorem c1343104 : checkChunk 1343104 128 = true := by decide +kernel
private theorem c1343232 : checkChunk 1343232 128 = true := by decide +kernel
private theorem c1343360 : checkChunk 1343360 128 = true := by decide +kernel

public theorem checked : Checked 1335296 1343488 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1335296 128 c1335296) (checkChunk_sound 1335424 128 c1335424)) (Checked.append (checkChunk_sound 1335552 128 c1335552) (checkChunk_sound 1335680 128 c1335680))) (Checked.append (Checked.append (checkChunk_sound 1335808 128 c1335808) (checkChunk_sound 1335936 128 c1335936)) (Checked.append (checkChunk_sound 1336064 128 c1336064) (checkChunk_sound 1336192 128 c1336192)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1336320 128 c1336320) (checkChunk_sound 1336448 128 c1336448)) (Checked.append (checkChunk_sound 1336576 128 c1336576) (checkChunk_sound 1336704 128 c1336704))) (Checked.append (Checked.append (checkChunk_sound 1336832 128 c1336832) (checkChunk_sound 1336960 128 c1336960)) (Checked.append (checkChunk_sound 1337088 128 c1337088) (checkChunk_sound 1337216 128 c1337216))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1337344 128 c1337344) (checkChunk_sound 1337472 128 c1337472)) (Checked.append (checkChunk_sound 1337600 128 c1337600) (checkChunk_sound 1337728 128 c1337728))) (Checked.append (Checked.append (checkChunk_sound 1337856 128 c1337856) (checkChunk_sound 1337984 128 c1337984)) (Checked.append (checkChunk_sound 1338112 128 c1338112) (checkChunk_sound 1338240 128 c1338240)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1338368 128 c1338368) (checkChunk_sound 1338496 128 c1338496)) (Checked.append (checkChunk_sound 1338624 128 c1338624) (checkChunk_sound 1338752 128 c1338752))) (Checked.append (Checked.append (checkChunk_sound 1338880 128 c1338880) (checkChunk_sound 1339008 128 c1339008)) (Checked.append (checkChunk_sound 1339136 128 c1339136) (checkChunk_sound 1339264 128 c1339264)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1339392 128 c1339392) (checkChunk_sound 1339520 128 c1339520)) (Checked.append (checkChunk_sound 1339648 128 c1339648) (checkChunk_sound 1339776 128 c1339776))) (Checked.append (Checked.append (checkChunk_sound 1339904 128 c1339904) (checkChunk_sound 1340032 128 c1340032)) (Checked.append (checkChunk_sound 1340160 128 c1340160) (checkChunk_sound 1340288 128 c1340288)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1340416 128 c1340416) (checkChunk_sound 1340544 128 c1340544)) (Checked.append (checkChunk_sound 1340672 128 c1340672) (checkChunk_sound 1340800 128 c1340800))) (Checked.append (Checked.append (checkChunk_sound 1340928 128 c1340928) (checkChunk_sound 1341056 128 c1341056)) (Checked.append (checkChunk_sound 1341184 128 c1341184) (checkChunk_sound 1341312 128 c1341312))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1341440 128 c1341440) (checkChunk_sound 1341568 128 c1341568)) (Checked.append (checkChunk_sound 1341696 128 c1341696) (checkChunk_sound 1341824 128 c1341824))) (Checked.append (Checked.append (checkChunk_sound 1341952 128 c1341952) (checkChunk_sound 1342080 128 c1342080)) (Checked.append (checkChunk_sound 1342208 128 c1342208) (checkChunk_sound 1342336 128 c1342336)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1342464 128 c1342464) (checkChunk_sound 1342592 128 c1342592)) (Checked.append (checkChunk_sound 1342720 128 c1342720) (checkChunk_sound 1342848 128 c1342848))) (Checked.append (Checked.append (checkChunk_sound 1342976 128 c1342976) (checkChunk_sound 1343104 128 c1343104)) (Checked.append (checkChunk_sound 1343232 128 c1343232) (checkChunk_sound 1343360 128 c1343360)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B006
