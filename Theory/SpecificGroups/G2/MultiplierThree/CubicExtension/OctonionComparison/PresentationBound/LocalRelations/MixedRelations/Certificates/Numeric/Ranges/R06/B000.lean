module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1286144, 1294336).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B000
private theorem c1286144 : checkChunk 1286144 128 = true := by decide +kernel
private theorem c1286272 : checkChunk 1286272 128 = true := by decide +kernel
private theorem c1286400 : checkChunk 1286400 128 = true := by decide +kernel
private theorem c1286528 : checkChunk 1286528 128 = true := by decide +kernel
private theorem c1286656 : checkChunk 1286656 128 = true := by decide +kernel
private theorem c1286784 : checkChunk 1286784 128 = true := by decide +kernel
private theorem c1286912 : checkChunk 1286912 128 = true := by decide +kernel
private theorem c1287040 : checkChunk 1287040 128 = true := by decide +kernel
private theorem c1287168 : checkChunk 1287168 128 = true := by decide +kernel
private theorem c1287296 : checkChunk 1287296 128 = true := by decide +kernel
private theorem c1287424 : checkChunk 1287424 128 = true := by decide +kernel
private theorem c1287552 : checkChunk 1287552 128 = true := by decide +kernel
private theorem c1287680 : checkChunk 1287680 128 = true := by decide +kernel
private theorem c1287808 : checkChunk 1287808 128 = true := by decide +kernel
private theorem c1287936 : checkChunk 1287936 128 = true := by decide +kernel
private theorem c1288064 : checkChunk 1288064 128 = true := by decide +kernel
private theorem c1288192 : checkChunk 1288192 128 = true := by decide +kernel
private theorem c1288320 : checkChunk 1288320 128 = true := by decide +kernel
private theorem c1288448 : checkChunk 1288448 128 = true := by decide +kernel
private theorem c1288576 : checkChunk 1288576 128 = true := by decide +kernel
private theorem c1288704 : checkChunk 1288704 128 = true := by decide +kernel
private theorem c1288832 : checkChunk 1288832 128 = true := by decide +kernel
private theorem c1288960 : checkChunk 1288960 128 = true := by decide +kernel
private theorem c1289088 : checkChunk 1289088 128 = true := by decide +kernel
private theorem c1289216 : checkChunk 1289216 128 = true := by decide +kernel
private theorem c1289344 : checkChunk 1289344 128 = true := by decide +kernel
private theorem c1289472 : checkChunk 1289472 128 = true := by decide +kernel
private theorem c1289600 : checkChunk 1289600 128 = true := by decide +kernel
private theorem c1289728 : checkChunk 1289728 128 = true := by decide +kernel
private theorem c1289856 : checkChunk 1289856 128 = true := by decide +kernel
private theorem c1289984 : checkChunk 1289984 128 = true := by decide +kernel
private theorem c1290112 : checkChunk 1290112 128 = true := by decide +kernel
private theorem c1290240 : checkChunk 1290240 128 = true := by decide +kernel
private theorem c1290368 : checkChunk 1290368 128 = true := by decide +kernel
private theorem c1290496 : checkChunk 1290496 128 = true := by decide +kernel
private theorem c1290624 : checkChunk 1290624 128 = true := by decide +kernel
private theorem c1290752 : checkChunk 1290752 128 = true := by decide +kernel
private theorem c1290880 : checkChunk 1290880 128 = true := by decide +kernel
private theorem c1291008 : checkChunk 1291008 128 = true := by decide +kernel
private theorem c1291136 : checkChunk 1291136 128 = true := by decide +kernel
private theorem c1291264 : checkChunk 1291264 128 = true := by decide +kernel
private theorem c1291392 : checkChunk 1291392 128 = true := by decide +kernel
private theorem c1291520 : checkChunk 1291520 128 = true := by decide +kernel
private theorem c1291648 : checkChunk 1291648 128 = true := by decide +kernel
private theorem c1291776 : checkChunk 1291776 128 = true := by decide +kernel
private theorem c1291904 : checkChunk 1291904 128 = true := by decide +kernel
private theorem c1292032 : checkChunk 1292032 128 = true := by decide +kernel
private theorem c1292160 : checkChunk 1292160 128 = true := by decide +kernel
private theorem c1292288 : checkChunk 1292288 128 = true := by decide +kernel
private theorem c1292416 : checkChunk 1292416 128 = true := by decide +kernel
private theorem c1292544 : checkChunk 1292544 128 = true := by decide +kernel
private theorem c1292672 : checkChunk 1292672 128 = true := by decide +kernel
private theorem c1292800 : checkChunk 1292800 128 = true := by decide +kernel
private theorem c1292928 : checkChunk 1292928 128 = true := by decide +kernel
private theorem c1293056 : checkChunk 1293056 128 = true := by decide +kernel
private theorem c1293184 : checkChunk 1293184 128 = true := by decide +kernel
private theorem c1293312 : checkChunk 1293312 128 = true := by decide +kernel
private theorem c1293440 : checkChunk 1293440 128 = true := by decide +kernel
private theorem c1293568 : checkChunk 1293568 128 = true := by decide +kernel
private theorem c1293696 : checkChunk 1293696 128 = true := by decide +kernel
private theorem c1293824 : checkChunk 1293824 128 = true := by decide +kernel
private theorem c1293952 : checkChunk 1293952 128 = true := by decide +kernel
private theorem c1294080 : checkChunk 1294080 128 = true := by decide +kernel
private theorem c1294208 : checkChunk 1294208 128 = true := by decide +kernel

public theorem checked : Checked 1286144 1294336 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1286144 128 c1286144) (checkChunk_sound 1286272 128 c1286272)) (Checked.append (checkChunk_sound 1286400 128 c1286400) (checkChunk_sound 1286528 128 c1286528))) (Checked.append (Checked.append (checkChunk_sound 1286656 128 c1286656) (checkChunk_sound 1286784 128 c1286784)) (Checked.append (checkChunk_sound 1286912 128 c1286912) (checkChunk_sound 1287040 128 c1287040)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1287168 128 c1287168) (checkChunk_sound 1287296 128 c1287296)) (Checked.append (checkChunk_sound 1287424 128 c1287424) (checkChunk_sound 1287552 128 c1287552))) (Checked.append (Checked.append (checkChunk_sound 1287680 128 c1287680) (checkChunk_sound 1287808 128 c1287808)) (Checked.append (checkChunk_sound 1287936 128 c1287936) (checkChunk_sound 1288064 128 c1288064))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1288192 128 c1288192) (checkChunk_sound 1288320 128 c1288320)) (Checked.append (checkChunk_sound 1288448 128 c1288448) (checkChunk_sound 1288576 128 c1288576))) (Checked.append (Checked.append (checkChunk_sound 1288704 128 c1288704) (checkChunk_sound 1288832 128 c1288832)) (Checked.append (checkChunk_sound 1288960 128 c1288960) (checkChunk_sound 1289088 128 c1289088)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1289216 128 c1289216) (checkChunk_sound 1289344 128 c1289344)) (Checked.append (checkChunk_sound 1289472 128 c1289472) (checkChunk_sound 1289600 128 c1289600))) (Checked.append (Checked.append (checkChunk_sound 1289728 128 c1289728) (checkChunk_sound 1289856 128 c1289856)) (Checked.append (checkChunk_sound 1289984 128 c1289984) (checkChunk_sound 1290112 128 c1290112)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1290240 128 c1290240) (checkChunk_sound 1290368 128 c1290368)) (Checked.append (checkChunk_sound 1290496 128 c1290496) (checkChunk_sound 1290624 128 c1290624))) (Checked.append (Checked.append (checkChunk_sound 1290752 128 c1290752) (checkChunk_sound 1290880 128 c1290880)) (Checked.append (checkChunk_sound 1291008 128 c1291008) (checkChunk_sound 1291136 128 c1291136)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1291264 128 c1291264) (checkChunk_sound 1291392 128 c1291392)) (Checked.append (checkChunk_sound 1291520 128 c1291520) (checkChunk_sound 1291648 128 c1291648))) (Checked.append (Checked.append (checkChunk_sound 1291776 128 c1291776) (checkChunk_sound 1291904 128 c1291904)) (Checked.append (checkChunk_sound 1292032 128 c1292032) (checkChunk_sound 1292160 128 c1292160))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1292288 128 c1292288) (checkChunk_sound 1292416 128 c1292416)) (Checked.append (checkChunk_sound 1292544 128 c1292544) (checkChunk_sound 1292672 128 c1292672))) (Checked.append (Checked.append (checkChunk_sound 1292800 128 c1292800) (checkChunk_sound 1292928 128 c1292928)) (Checked.append (checkChunk_sound 1293056 128 c1293056) (checkChunk_sound 1293184 128 c1293184)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1293312 128 c1293312) (checkChunk_sound 1293440 128 c1293440)) (Checked.append (checkChunk_sound 1293568 128 c1293568) (checkChunk_sound 1293696 128 c1293696))) (Checked.append (Checked.append (checkChunk_sound 1293824 128 c1293824) (checkChunk_sound 1293952 128 c1293952)) (Checked.append (checkChunk_sound 1294080 128 c1294080) (checkChunk_sound 1294208 128 c1294208)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B000
