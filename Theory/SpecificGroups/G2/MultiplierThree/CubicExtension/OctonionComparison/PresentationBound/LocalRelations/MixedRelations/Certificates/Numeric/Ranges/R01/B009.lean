module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [294912, 303104).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B009
private theorem c294912 : checkChunk 294912 128 = true := by decide +kernel
private theorem c295040 : checkChunk 295040 128 = true := by decide +kernel
private theorem c295168 : checkChunk 295168 128 = true := by decide +kernel
private theorem c295296 : checkChunk 295296 128 = true := by decide +kernel
private theorem c295424 : checkChunk 295424 128 = true := by decide +kernel
private theorem c295552 : checkChunk 295552 128 = true := by decide +kernel
private theorem c295680 : checkChunk 295680 128 = true := by decide +kernel
private theorem c295808 : checkChunk 295808 128 = true := by decide +kernel
private theorem c295936 : checkChunk 295936 128 = true := by decide +kernel
private theorem c296064 : checkChunk 296064 128 = true := by decide +kernel
private theorem c296192 : checkChunk 296192 128 = true := by decide +kernel
private theorem c296320 : checkChunk 296320 128 = true := by decide +kernel
private theorem c296448 : checkChunk 296448 128 = true := by decide +kernel
private theorem c296576 : checkChunk 296576 128 = true := by decide +kernel
private theorem c296704 : checkChunk 296704 128 = true := by decide +kernel
private theorem c296832 : checkChunk 296832 128 = true := by decide +kernel
private theorem c296960 : checkChunk 296960 128 = true := by decide +kernel
private theorem c297088 : checkChunk 297088 128 = true := by decide +kernel
private theorem c297216 : checkChunk 297216 128 = true := by decide +kernel
private theorem c297344 : checkChunk 297344 128 = true := by decide +kernel
private theorem c297472 : checkChunk 297472 128 = true := by decide +kernel
private theorem c297600 : checkChunk 297600 128 = true := by decide +kernel
private theorem c297728 : checkChunk 297728 128 = true := by decide +kernel
private theorem c297856 : checkChunk 297856 128 = true := by decide +kernel
private theorem c297984 : checkChunk 297984 128 = true := by decide +kernel
private theorem c298112 : checkChunk 298112 128 = true := by decide +kernel
private theorem c298240 : checkChunk 298240 128 = true := by decide +kernel
private theorem c298368 : checkChunk 298368 128 = true := by decide +kernel
private theorem c298496 : checkChunk 298496 128 = true := by decide +kernel
private theorem c298624 : checkChunk 298624 128 = true := by decide +kernel
private theorem c298752 : checkChunk 298752 128 = true := by decide +kernel
private theorem c298880 : checkChunk 298880 128 = true := by decide +kernel
private theorem c299008 : checkChunk 299008 128 = true := by decide +kernel
private theorem c299136 : checkChunk 299136 128 = true := by decide +kernel
private theorem c299264 : checkChunk 299264 128 = true := by decide +kernel
private theorem c299392 : checkChunk 299392 128 = true := by decide +kernel
private theorem c299520 : checkChunk 299520 128 = true := by decide +kernel
private theorem c299648 : checkChunk 299648 128 = true := by decide +kernel
private theorem c299776 : checkChunk 299776 128 = true := by decide +kernel
private theorem c299904 : checkChunk 299904 128 = true := by decide +kernel
private theorem c300032 : checkChunk 300032 128 = true := by decide +kernel
private theorem c300160 : checkChunk 300160 128 = true := by decide +kernel
private theorem c300288 : checkChunk 300288 128 = true := by decide +kernel
private theorem c300416 : checkChunk 300416 128 = true := by decide +kernel
private theorem c300544 : checkChunk 300544 128 = true := by decide +kernel
private theorem c300672 : checkChunk 300672 128 = true := by decide +kernel
private theorem c300800 : checkChunk 300800 128 = true := by decide +kernel
private theorem c300928 : checkChunk 300928 128 = true := by decide +kernel
private theorem c301056 : checkChunk 301056 128 = true := by decide +kernel
private theorem c301184 : checkChunk 301184 128 = true := by decide +kernel
private theorem c301312 : checkChunk 301312 128 = true := by decide +kernel
private theorem c301440 : checkChunk 301440 128 = true := by decide +kernel
private theorem c301568 : checkChunk 301568 128 = true := by decide +kernel
private theorem c301696 : checkChunk 301696 128 = true := by decide +kernel
private theorem c301824 : checkChunk 301824 128 = true := by decide +kernel
private theorem c301952 : checkChunk 301952 128 = true := by decide +kernel
private theorem c302080 : checkChunk 302080 128 = true := by decide +kernel
private theorem c302208 : checkChunk 302208 128 = true := by decide +kernel
private theorem c302336 : checkChunk 302336 128 = true := by decide +kernel
private theorem c302464 : checkChunk 302464 128 = true := by decide +kernel
private theorem c302592 : checkChunk 302592 128 = true := by decide +kernel
private theorem c302720 : checkChunk 302720 128 = true := by decide +kernel
private theorem c302848 : checkChunk 302848 128 = true := by decide +kernel
private theorem c302976 : checkChunk 302976 128 = true := by decide +kernel

public theorem checked : Checked 294912 303104 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 294912 128 c294912) (checkChunk_sound 295040 128 c295040)) (Checked.append (checkChunk_sound 295168 128 c295168) (checkChunk_sound 295296 128 c295296))) (Checked.append (Checked.append (checkChunk_sound 295424 128 c295424) (checkChunk_sound 295552 128 c295552)) (Checked.append (checkChunk_sound 295680 128 c295680) (checkChunk_sound 295808 128 c295808)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 295936 128 c295936) (checkChunk_sound 296064 128 c296064)) (Checked.append (checkChunk_sound 296192 128 c296192) (checkChunk_sound 296320 128 c296320))) (Checked.append (Checked.append (checkChunk_sound 296448 128 c296448) (checkChunk_sound 296576 128 c296576)) (Checked.append (checkChunk_sound 296704 128 c296704) (checkChunk_sound 296832 128 c296832))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 296960 128 c296960) (checkChunk_sound 297088 128 c297088)) (Checked.append (checkChunk_sound 297216 128 c297216) (checkChunk_sound 297344 128 c297344))) (Checked.append (Checked.append (checkChunk_sound 297472 128 c297472) (checkChunk_sound 297600 128 c297600)) (Checked.append (checkChunk_sound 297728 128 c297728) (checkChunk_sound 297856 128 c297856)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 297984 128 c297984) (checkChunk_sound 298112 128 c298112)) (Checked.append (checkChunk_sound 298240 128 c298240) (checkChunk_sound 298368 128 c298368))) (Checked.append (Checked.append (checkChunk_sound 298496 128 c298496) (checkChunk_sound 298624 128 c298624)) (Checked.append (checkChunk_sound 298752 128 c298752) (checkChunk_sound 298880 128 c298880)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 299008 128 c299008) (checkChunk_sound 299136 128 c299136)) (Checked.append (checkChunk_sound 299264 128 c299264) (checkChunk_sound 299392 128 c299392))) (Checked.append (Checked.append (checkChunk_sound 299520 128 c299520) (checkChunk_sound 299648 128 c299648)) (Checked.append (checkChunk_sound 299776 128 c299776) (checkChunk_sound 299904 128 c299904)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 300032 128 c300032) (checkChunk_sound 300160 128 c300160)) (Checked.append (checkChunk_sound 300288 128 c300288) (checkChunk_sound 300416 128 c300416))) (Checked.append (Checked.append (checkChunk_sound 300544 128 c300544) (checkChunk_sound 300672 128 c300672)) (Checked.append (checkChunk_sound 300800 128 c300800) (checkChunk_sound 300928 128 c300928))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 301056 128 c301056) (checkChunk_sound 301184 128 c301184)) (Checked.append (checkChunk_sound 301312 128 c301312) (checkChunk_sound 301440 128 c301440))) (Checked.append (Checked.append (checkChunk_sound 301568 128 c301568) (checkChunk_sound 301696 128 c301696)) (Checked.append (checkChunk_sound 301824 128 c301824) (checkChunk_sound 301952 128 c301952)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 302080 128 c302080) (checkChunk_sound 302208 128 c302208)) (Checked.append (checkChunk_sound 302336 128 c302336) (checkChunk_sound 302464 128 c302464))) (Checked.append (Checked.append (checkChunk_sound 302592 128 c302592) (checkChunk_sound 302720 128 c302720)) (Checked.append (checkChunk_sound 302848 128 c302848) (checkChunk_sound 302976 128 c302976)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B009
