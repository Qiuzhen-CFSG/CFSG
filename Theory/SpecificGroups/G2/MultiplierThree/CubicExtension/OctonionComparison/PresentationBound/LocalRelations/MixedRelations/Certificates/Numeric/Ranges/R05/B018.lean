module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1220608, 1228800).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B018
private theorem c1220608 : checkChunk 1220608 128 = true := by decide +kernel
private theorem c1220736 : checkChunk 1220736 128 = true := by decide +kernel
private theorem c1220864 : checkChunk 1220864 128 = true := by decide +kernel
private theorem c1220992 : checkChunk 1220992 128 = true := by decide +kernel
private theorem c1221120 : checkChunk 1221120 128 = true := by decide +kernel
private theorem c1221248 : checkChunk 1221248 128 = true := by decide +kernel
private theorem c1221376 : checkChunk 1221376 128 = true := by decide +kernel
private theorem c1221504 : checkChunk 1221504 128 = true := by decide +kernel
private theorem c1221632 : checkChunk 1221632 128 = true := by decide +kernel
private theorem c1221760 : checkChunk 1221760 128 = true := by decide +kernel
private theorem c1221888 : checkChunk 1221888 128 = true := by decide +kernel
private theorem c1222016 : checkChunk 1222016 128 = true := by decide +kernel
private theorem c1222144 : checkChunk 1222144 128 = true := by decide +kernel
private theorem c1222272 : checkChunk 1222272 128 = true := by decide +kernel
private theorem c1222400 : checkChunk 1222400 128 = true := by decide +kernel
private theorem c1222528 : checkChunk 1222528 128 = true := by decide +kernel
private theorem c1222656 : checkChunk 1222656 128 = true := by decide +kernel
private theorem c1222784 : checkChunk 1222784 128 = true := by decide +kernel
private theorem c1222912 : checkChunk 1222912 128 = true := by decide +kernel
private theorem c1223040 : checkChunk 1223040 128 = true := by decide +kernel
private theorem c1223168 : checkChunk 1223168 128 = true := by decide +kernel
private theorem c1223296 : checkChunk 1223296 128 = true := by decide +kernel
private theorem c1223424 : checkChunk 1223424 128 = true := by decide +kernel
private theorem c1223552 : checkChunk 1223552 128 = true := by decide +kernel
private theorem c1223680 : checkChunk 1223680 128 = true := by decide +kernel
private theorem c1223808 : checkChunk 1223808 128 = true := by decide +kernel
private theorem c1223936 : checkChunk 1223936 128 = true := by decide +kernel
private theorem c1224064 : checkChunk 1224064 128 = true := by decide +kernel
private theorem c1224192 : checkChunk 1224192 128 = true := by decide +kernel
private theorem c1224320 : checkChunk 1224320 128 = true := by decide +kernel
private theorem c1224448 : checkChunk 1224448 128 = true := by decide +kernel
private theorem c1224576 : checkChunk 1224576 128 = true := by decide +kernel
private theorem c1224704 : checkChunk 1224704 128 = true := by decide +kernel
private theorem c1224832 : checkChunk 1224832 128 = true := by decide +kernel
private theorem c1224960 : checkChunk 1224960 128 = true := by decide +kernel
private theorem c1225088 : checkChunk 1225088 128 = true := by decide +kernel
private theorem c1225216 : checkChunk 1225216 128 = true := by decide +kernel
private theorem c1225344 : checkChunk 1225344 128 = true := by decide +kernel
private theorem c1225472 : checkChunk 1225472 128 = true := by decide +kernel
private theorem c1225600 : checkChunk 1225600 128 = true := by decide +kernel
private theorem c1225728 : checkChunk 1225728 128 = true := by decide +kernel
private theorem c1225856 : checkChunk 1225856 128 = true := by decide +kernel
private theorem c1225984 : checkChunk 1225984 128 = true := by decide +kernel
private theorem c1226112 : checkChunk 1226112 128 = true := by decide +kernel
private theorem c1226240 : checkChunk 1226240 128 = true := by decide +kernel
private theorem c1226368 : checkChunk 1226368 128 = true := by decide +kernel
private theorem c1226496 : checkChunk 1226496 128 = true := by decide +kernel
private theorem c1226624 : checkChunk 1226624 128 = true := by decide +kernel
private theorem c1226752 : checkChunk 1226752 128 = true := by decide +kernel
private theorem c1226880 : checkChunk 1226880 128 = true := by decide +kernel
private theorem c1227008 : checkChunk 1227008 128 = true := by decide +kernel
private theorem c1227136 : checkChunk 1227136 128 = true := by decide +kernel
private theorem c1227264 : checkChunk 1227264 128 = true := by decide +kernel
private theorem c1227392 : checkChunk 1227392 128 = true := by decide +kernel
private theorem c1227520 : checkChunk 1227520 128 = true := by decide +kernel
private theorem c1227648 : checkChunk 1227648 128 = true := by decide +kernel
private theorem c1227776 : checkChunk 1227776 128 = true := by decide +kernel
private theorem c1227904 : checkChunk 1227904 128 = true := by decide +kernel
private theorem c1228032 : checkChunk 1228032 128 = true := by decide +kernel
private theorem c1228160 : checkChunk 1228160 128 = true := by decide +kernel
private theorem c1228288 : checkChunk 1228288 128 = true := by decide +kernel
private theorem c1228416 : checkChunk 1228416 128 = true := by decide +kernel
private theorem c1228544 : checkChunk 1228544 128 = true := by decide +kernel
private theorem c1228672 : checkChunk 1228672 128 = true := by decide +kernel

public theorem checked : Checked 1220608 1228800 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1220608 128 c1220608) (checkChunk_sound 1220736 128 c1220736)) (Checked.append (checkChunk_sound 1220864 128 c1220864) (checkChunk_sound 1220992 128 c1220992))) (Checked.append (Checked.append (checkChunk_sound 1221120 128 c1221120) (checkChunk_sound 1221248 128 c1221248)) (Checked.append (checkChunk_sound 1221376 128 c1221376) (checkChunk_sound 1221504 128 c1221504)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1221632 128 c1221632) (checkChunk_sound 1221760 128 c1221760)) (Checked.append (checkChunk_sound 1221888 128 c1221888) (checkChunk_sound 1222016 128 c1222016))) (Checked.append (Checked.append (checkChunk_sound 1222144 128 c1222144) (checkChunk_sound 1222272 128 c1222272)) (Checked.append (checkChunk_sound 1222400 128 c1222400) (checkChunk_sound 1222528 128 c1222528))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1222656 128 c1222656) (checkChunk_sound 1222784 128 c1222784)) (Checked.append (checkChunk_sound 1222912 128 c1222912) (checkChunk_sound 1223040 128 c1223040))) (Checked.append (Checked.append (checkChunk_sound 1223168 128 c1223168) (checkChunk_sound 1223296 128 c1223296)) (Checked.append (checkChunk_sound 1223424 128 c1223424) (checkChunk_sound 1223552 128 c1223552)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1223680 128 c1223680) (checkChunk_sound 1223808 128 c1223808)) (Checked.append (checkChunk_sound 1223936 128 c1223936) (checkChunk_sound 1224064 128 c1224064))) (Checked.append (Checked.append (checkChunk_sound 1224192 128 c1224192) (checkChunk_sound 1224320 128 c1224320)) (Checked.append (checkChunk_sound 1224448 128 c1224448) (checkChunk_sound 1224576 128 c1224576)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1224704 128 c1224704) (checkChunk_sound 1224832 128 c1224832)) (Checked.append (checkChunk_sound 1224960 128 c1224960) (checkChunk_sound 1225088 128 c1225088))) (Checked.append (Checked.append (checkChunk_sound 1225216 128 c1225216) (checkChunk_sound 1225344 128 c1225344)) (Checked.append (checkChunk_sound 1225472 128 c1225472) (checkChunk_sound 1225600 128 c1225600)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1225728 128 c1225728) (checkChunk_sound 1225856 128 c1225856)) (Checked.append (checkChunk_sound 1225984 128 c1225984) (checkChunk_sound 1226112 128 c1226112))) (Checked.append (Checked.append (checkChunk_sound 1226240 128 c1226240) (checkChunk_sound 1226368 128 c1226368)) (Checked.append (checkChunk_sound 1226496 128 c1226496) (checkChunk_sound 1226624 128 c1226624))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1226752 128 c1226752) (checkChunk_sound 1226880 128 c1226880)) (Checked.append (checkChunk_sound 1227008 128 c1227008) (checkChunk_sound 1227136 128 c1227136))) (Checked.append (Checked.append (checkChunk_sound 1227264 128 c1227264) (checkChunk_sound 1227392 128 c1227392)) (Checked.append (checkChunk_sound 1227520 128 c1227520) (checkChunk_sound 1227648 128 c1227648)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1227776 128 c1227776) (checkChunk_sound 1227904 128 c1227904)) (Checked.append (checkChunk_sound 1228032 128 c1228032) (checkChunk_sound 1228160 128 c1228160))) (Checked.append (Checked.append (checkChunk_sound 1228288 128 c1228288) (checkChunk_sound 1228416 128 c1228416)) (Checked.append (checkChunk_sound 1228544 128 c1228544) (checkChunk_sound 1228672 128 c1228672)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05.B018
