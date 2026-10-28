module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [172032, 180224).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B020
private theorem c172032 : checkChunk 172032 128 = true := by decide +kernel
private theorem c172160 : checkChunk 172160 128 = true := by decide +kernel
private theorem c172288 : checkChunk 172288 128 = true := by decide +kernel
private theorem c172416 : checkChunk 172416 128 = true := by decide +kernel
private theorem c172544 : checkChunk 172544 128 = true := by decide +kernel
private theorem c172672 : checkChunk 172672 128 = true := by decide +kernel
private theorem c172800 : checkChunk 172800 128 = true := by decide +kernel
private theorem c172928 : checkChunk 172928 128 = true := by decide +kernel
private theorem c173056 : checkChunk 173056 128 = true := by decide +kernel
private theorem c173184 : checkChunk 173184 128 = true := by decide +kernel
private theorem c173312 : checkChunk 173312 128 = true := by decide +kernel
private theorem c173440 : checkChunk 173440 128 = true := by decide +kernel
private theorem c173568 : checkChunk 173568 128 = true := by decide +kernel
private theorem c173696 : checkChunk 173696 128 = true := by decide +kernel
private theorem c173824 : checkChunk 173824 128 = true := by decide +kernel
private theorem c173952 : checkChunk 173952 128 = true := by decide +kernel
private theorem c174080 : checkChunk 174080 128 = true := by decide +kernel
private theorem c174208 : checkChunk 174208 128 = true := by decide +kernel
private theorem c174336 : checkChunk 174336 128 = true := by decide +kernel
private theorem c174464 : checkChunk 174464 128 = true := by decide +kernel
private theorem c174592 : checkChunk 174592 128 = true := by decide +kernel
private theorem c174720 : checkChunk 174720 128 = true := by decide +kernel
private theorem c174848 : checkChunk 174848 128 = true := by decide +kernel
private theorem c174976 : checkChunk 174976 128 = true := by decide +kernel
private theorem c175104 : checkChunk 175104 128 = true := by decide +kernel
private theorem c175232 : checkChunk 175232 128 = true := by decide +kernel
private theorem c175360 : checkChunk 175360 128 = true := by decide +kernel
private theorem c175488 : checkChunk 175488 128 = true := by decide +kernel
private theorem c175616 : checkChunk 175616 128 = true := by decide +kernel
private theorem c175744 : checkChunk 175744 128 = true := by decide +kernel
private theorem c175872 : checkChunk 175872 128 = true := by decide +kernel
private theorem c176000 : checkChunk 176000 128 = true := by decide +kernel
private theorem c176128 : checkChunk 176128 128 = true := by decide +kernel
private theorem c176256 : checkChunk 176256 128 = true := by decide +kernel
private theorem c176384 : checkChunk 176384 128 = true := by decide +kernel
private theorem c176512 : checkChunk 176512 128 = true := by decide +kernel
private theorem c176640 : checkChunk 176640 128 = true := by decide +kernel
private theorem c176768 : checkChunk 176768 128 = true := by decide +kernel
private theorem c176896 : checkChunk 176896 128 = true := by decide +kernel
private theorem c177024 : checkChunk 177024 128 = true := by decide +kernel
private theorem c177152 : checkChunk 177152 128 = true := by decide +kernel
private theorem c177280 : checkChunk 177280 128 = true := by decide +kernel
private theorem c177408 : checkChunk 177408 128 = true := by decide +kernel
private theorem c177536 : checkChunk 177536 128 = true := by decide +kernel
private theorem c177664 : checkChunk 177664 128 = true := by decide +kernel
private theorem c177792 : checkChunk 177792 128 = true := by decide +kernel
private theorem c177920 : checkChunk 177920 128 = true := by decide +kernel
private theorem c178048 : checkChunk 178048 128 = true := by decide +kernel
private theorem c178176 : checkChunk 178176 128 = true := by decide +kernel
private theorem c178304 : checkChunk 178304 128 = true := by decide +kernel
private theorem c178432 : checkChunk 178432 128 = true := by decide +kernel
private theorem c178560 : checkChunk 178560 128 = true := by decide +kernel
private theorem c178688 : checkChunk 178688 128 = true := by decide +kernel
private theorem c178816 : checkChunk 178816 128 = true := by decide +kernel
private theorem c178944 : checkChunk 178944 128 = true := by decide +kernel
private theorem c179072 : checkChunk 179072 128 = true := by decide +kernel
private theorem c179200 : checkChunk 179200 128 = true := by decide +kernel
private theorem c179328 : checkChunk 179328 128 = true := by decide +kernel
private theorem c179456 : checkChunk 179456 128 = true := by decide +kernel
private theorem c179584 : checkChunk 179584 128 = true := by decide +kernel
private theorem c179712 : checkChunk 179712 128 = true := by decide +kernel
private theorem c179840 : checkChunk 179840 128 = true := by decide +kernel
private theorem c179968 : checkChunk 179968 128 = true := by decide +kernel
private theorem c180096 : checkChunk 180096 128 = true := by decide +kernel

public theorem checked : Checked 172032 180224 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 172032 128 c172032) (checkChunk_sound 172160 128 c172160)) (Checked.append (checkChunk_sound 172288 128 c172288) (checkChunk_sound 172416 128 c172416))) (Checked.append (Checked.append (checkChunk_sound 172544 128 c172544) (checkChunk_sound 172672 128 c172672)) (Checked.append (checkChunk_sound 172800 128 c172800) (checkChunk_sound 172928 128 c172928)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 173056 128 c173056) (checkChunk_sound 173184 128 c173184)) (Checked.append (checkChunk_sound 173312 128 c173312) (checkChunk_sound 173440 128 c173440))) (Checked.append (Checked.append (checkChunk_sound 173568 128 c173568) (checkChunk_sound 173696 128 c173696)) (Checked.append (checkChunk_sound 173824 128 c173824) (checkChunk_sound 173952 128 c173952))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 174080 128 c174080) (checkChunk_sound 174208 128 c174208)) (Checked.append (checkChunk_sound 174336 128 c174336) (checkChunk_sound 174464 128 c174464))) (Checked.append (Checked.append (checkChunk_sound 174592 128 c174592) (checkChunk_sound 174720 128 c174720)) (Checked.append (checkChunk_sound 174848 128 c174848) (checkChunk_sound 174976 128 c174976)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 175104 128 c175104) (checkChunk_sound 175232 128 c175232)) (Checked.append (checkChunk_sound 175360 128 c175360) (checkChunk_sound 175488 128 c175488))) (Checked.append (Checked.append (checkChunk_sound 175616 128 c175616) (checkChunk_sound 175744 128 c175744)) (Checked.append (checkChunk_sound 175872 128 c175872) (checkChunk_sound 176000 128 c176000)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 176128 128 c176128) (checkChunk_sound 176256 128 c176256)) (Checked.append (checkChunk_sound 176384 128 c176384) (checkChunk_sound 176512 128 c176512))) (Checked.append (Checked.append (checkChunk_sound 176640 128 c176640) (checkChunk_sound 176768 128 c176768)) (Checked.append (checkChunk_sound 176896 128 c176896) (checkChunk_sound 177024 128 c177024)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 177152 128 c177152) (checkChunk_sound 177280 128 c177280)) (Checked.append (checkChunk_sound 177408 128 c177408) (checkChunk_sound 177536 128 c177536))) (Checked.append (Checked.append (checkChunk_sound 177664 128 c177664) (checkChunk_sound 177792 128 c177792)) (Checked.append (checkChunk_sound 177920 128 c177920) (checkChunk_sound 178048 128 c178048))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 178176 128 c178176) (checkChunk_sound 178304 128 c178304)) (Checked.append (checkChunk_sound 178432 128 c178432) (checkChunk_sound 178560 128 c178560))) (Checked.append (Checked.append (checkChunk_sound 178688 128 c178688) (checkChunk_sound 178816 128 c178816)) (Checked.append (checkChunk_sound 178944 128 c178944) (checkChunk_sound 179072 128 c179072)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 179200 128 c179200) (checkChunk_sound 179328 128 c179328)) (Checked.append (checkChunk_sound 179456 128 c179456) (checkChunk_sound 179584 128 c179584))) (Checked.append (Checked.append (checkChunk_sound 179712 128 c179712) (checkChunk_sound 179840 128 c179840)) (Checked.append (checkChunk_sound 179968 128 c179968) (checkChunk_sound 180096 128 c180096)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B020
