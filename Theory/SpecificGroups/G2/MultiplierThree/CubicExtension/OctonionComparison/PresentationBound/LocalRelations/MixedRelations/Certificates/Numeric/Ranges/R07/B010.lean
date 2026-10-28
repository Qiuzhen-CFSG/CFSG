module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1581056, 1589248).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B010
private theorem c1581056 : checkChunk 1581056 128 = true := by decide +kernel
private theorem c1581184 : checkChunk 1581184 128 = true := by decide +kernel
private theorem c1581312 : checkChunk 1581312 128 = true := by decide +kernel
private theorem c1581440 : checkChunk 1581440 128 = true := by decide +kernel
private theorem c1581568 : checkChunk 1581568 128 = true := by decide +kernel
private theorem c1581696 : checkChunk 1581696 128 = true := by decide +kernel
private theorem c1581824 : checkChunk 1581824 128 = true := by decide +kernel
private theorem c1581952 : checkChunk 1581952 128 = true := by decide +kernel
private theorem c1582080 : checkChunk 1582080 128 = true := by decide +kernel
private theorem c1582208 : checkChunk 1582208 128 = true := by decide +kernel
private theorem c1582336 : checkChunk 1582336 128 = true := by decide +kernel
private theorem c1582464 : checkChunk 1582464 128 = true := by decide +kernel
private theorem c1582592 : checkChunk 1582592 128 = true := by decide +kernel
private theorem c1582720 : checkChunk 1582720 128 = true := by decide +kernel
private theorem c1582848 : checkChunk 1582848 128 = true := by decide +kernel
private theorem c1582976 : checkChunk 1582976 128 = true := by decide +kernel
private theorem c1583104 : checkChunk 1583104 128 = true := by decide +kernel
private theorem c1583232 : checkChunk 1583232 128 = true := by decide +kernel
private theorem c1583360 : checkChunk 1583360 128 = true := by decide +kernel
private theorem c1583488 : checkChunk 1583488 128 = true := by decide +kernel
private theorem c1583616 : checkChunk 1583616 128 = true := by decide +kernel
private theorem c1583744 : checkChunk 1583744 128 = true := by decide +kernel
private theorem c1583872 : checkChunk 1583872 128 = true := by decide +kernel
private theorem c1584000 : checkChunk 1584000 128 = true := by decide +kernel
private theorem c1584128 : checkChunk 1584128 128 = true := by decide +kernel
private theorem c1584256 : checkChunk 1584256 128 = true := by decide +kernel
private theorem c1584384 : checkChunk 1584384 128 = true := by decide +kernel
private theorem c1584512 : checkChunk 1584512 128 = true := by decide +kernel
private theorem c1584640 : checkChunk 1584640 128 = true := by decide +kernel
private theorem c1584768 : checkChunk 1584768 128 = true := by decide +kernel
private theorem c1584896 : checkChunk 1584896 128 = true := by decide +kernel
private theorem c1585024 : checkChunk 1585024 128 = true := by decide +kernel
private theorem c1585152 : checkChunk 1585152 128 = true := by decide +kernel
private theorem c1585280 : checkChunk 1585280 128 = true := by decide +kernel
private theorem c1585408 : checkChunk 1585408 128 = true := by decide +kernel
private theorem c1585536 : checkChunk 1585536 128 = true := by decide +kernel
private theorem c1585664 : checkChunk 1585664 128 = true := by decide +kernel
private theorem c1585792 : checkChunk 1585792 128 = true := by decide +kernel
private theorem c1585920 : checkChunk 1585920 128 = true := by decide +kernel
private theorem c1586048 : checkChunk 1586048 128 = true := by decide +kernel
private theorem c1586176 : checkChunk 1586176 128 = true := by decide +kernel
private theorem c1586304 : checkChunk 1586304 128 = true := by decide +kernel
private theorem c1586432 : checkChunk 1586432 128 = true := by decide +kernel
private theorem c1586560 : checkChunk 1586560 128 = true := by decide +kernel
private theorem c1586688 : checkChunk 1586688 128 = true := by decide +kernel
private theorem c1586816 : checkChunk 1586816 128 = true := by decide +kernel
private theorem c1586944 : checkChunk 1586944 128 = true := by decide +kernel
private theorem c1587072 : checkChunk 1587072 128 = true := by decide +kernel
private theorem c1587200 : checkChunk 1587200 128 = true := by decide +kernel
private theorem c1587328 : checkChunk 1587328 128 = true := by decide +kernel
private theorem c1587456 : checkChunk 1587456 128 = true := by decide +kernel
private theorem c1587584 : checkChunk 1587584 128 = true := by decide +kernel
private theorem c1587712 : checkChunk 1587712 128 = true := by decide +kernel
private theorem c1587840 : checkChunk 1587840 128 = true := by decide +kernel
private theorem c1587968 : checkChunk 1587968 128 = true := by decide +kernel
private theorem c1588096 : checkChunk 1588096 128 = true := by decide +kernel
private theorem c1588224 : checkChunk 1588224 128 = true := by decide +kernel
private theorem c1588352 : checkChunk 1588352 128 = true := by decide +kernel
private theorem c1588480 : checkChunk 1588480 128 = true := by decide +kernel
private theorem c1588608 : checkChunk 1588608 128 = true := by decide +kernel
private theorem c1588736 : checkChunk 1588736 128 = true := by decide +kernel
private theorem c1588864 : checkChunk 1588864 128 = true := by decide +kernel
private theorem c1588992 : checkChunk 1588992 128 = true := by decide +kernel
private theorem c1589120 : checkChunk 1589120 128 = true := by decide +kernel

public theorem checked : Checked 1581056 1589248 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1581056 128 c1581056) (checkChunk_sound 1581184 128 c1581184)) (Checked.append (checkChunk_sound 1581312 128 c1581312) (checkChunk_sound 1581440 128 c1581440))) (Checked.append (Checked.append (checkChunk_sound 1581568 128 c1581568) (checkChunk_sound 1581696 128 c1581696)) (Checked.append (checkChunk_sound 1581824 128 c1581824) (checkChunk_sound 1581952 128 c1581952)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1582080 128 c1582080) (checkChunk_sound 1582208 128 c1582208)) (Checked.append (checkChunk_sound 1582336 128 c1582336) (checkChunk_sound 1582464 128 c1582464))) (Checked.append (Checked.append (checkChunk_sound 1582592 128 c1582592) (checkChunk_sound 1582720 128 c1582720)) (Checked.append (checkChunk_sound 1582848 128 c1582848) (checkChunk_sound 1582976 128 c1582976))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1583104 128 c1583104) (checkChunk_sound 1583232 128 c1583232)) (Checked.append (checkChunk_sound 1583360 128 c1583360) (checkChunk_sound 1583488 128 c1583488))) (Checked.append (Checked.append (checkChunk_sound 1583616 128 c1583616) (checkChunk_sound 1583744 128 c1583744)) (Checked.append (checkChunk_sound 1583872 128 c1583872) (checkChunk_sound 1584000 128 c1584000)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1584128 128 c1584128) (checkChunk_sound 1584256 128 c1584256)) (Checked.append (checkChunk_sound 1584384 128 c1584384) (checkChunk_sound 1584512 128 c1584512))) (Checked.append (Checked.append (checkChunk_sound 1584640 128 c1584640) (checkChunk_sound 1584768 128 c1584768)) (Checked.append (checkChunk_sound 1584896 128 c1584896) (checkChunk_sound 1585024 128 c1585024)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1585152 128 c1585152) (checkChunk_sound 1585280 128 c1585280)) (Checked.append (checkChunk_sound 1585408 128 c1585408) (checkChunk_sound 1585536 128 c1585536))) (Checked.append (Checked.append (checkChunk_sound 1585664 128 c1585664) (checkChunk_sound 1585792 128 c1585792)) (Checked.append (checkChunk_sound 1585920 128 c1585920) (checkChunk_sound 1586048 128 c1586048)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1586176 128 c1586176) (checkChunk_sound 1586304 128 c1586304)) (Checked.append (checkChunk_sound 1586432 128 c1586432) (checkChunk_sound 1586560 128 c1586560))) (Checked.append (Checked.append (checkChunk_sound 1586688 128 c1586688) (checkChunk_sound 1586816 128 c1586816)) (Checked.append (checkChunk_sound 1586944 128 c1586944) (checkChunk_sound 1587072 128 c1587072))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1587200 128 c1587200) (checkChunk_sound 1587328 128 c1587328)) (Checked.append (checkChunk_sound 1587456 128 c1587456) (checkChunk_sound 1587584 128 c1587584))) (Checked.append (Checked.append (checkChunk_sound 1587712 128 c1587712) (checkChunk_sound 1587840 128 c1587840)) (Checked.append (checkChunk_sound 1587968 128 c1587968) (checkChunk_sound 1588096 128 c1588096)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1588224 128 c1588224) (checkChunk_sound 1588352 128 c1588352)) (Checked.append (checkChunk_sound 1588480 128 c1588480) (checkChunk_sound 1588608 128 c1588608))) (Checked.append (Checked.append (checkChunk_sound 1588736 128 c1588736) (checkChunk_sound 1588864 128 c1588864)) (Checked.append (checkChunk_sound 1588992 128 c1588992) (checkChunk_sound 1589120 128 c1589120)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B010
