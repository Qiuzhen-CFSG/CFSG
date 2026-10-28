module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [245760, 253952).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B003
private theorem c245760 : checkChunk 245760 128 = true := by decide +kernel
private theorem c245888 : checkChunk 245888 128 = true := by decide +kernel
private theorem c246016 : checkChunk 246016 128 = true := by decide +kernel
private theorem c246144 : checkChunk 246144 128 = true := by decide +kernel
private theorem c246272 : checkChunk 246272 128 = true := by decide +kernel
private theorem c246400 : checkChunk 246400 128 = true := by decide +kernel
private theorem c246528 : checkChunk 246528 128 = true := by decide +kernel
private theorem c246656 : checkChunk 246656 128 = true := by decide +kernel
private theorem c246784 : checkChunk 246784 128 = true := by decide +kernel
private theorem c246912 : checkChunk 246912 128 = true := by decide +kernel
private theorem c247040 : checkChunk 247040 128 = true := by decide +kernel
private theorem c247168 : checkChunk 247168 128 = true := by decide +kernel
private theorem c247296 : checkChunk 247296 128 = true := by decide +kernel
private theorem c247424 : checkChunk 247424 128 = true := by decide +kernel
private theorem c247552 : checkChunk 247552 128 = true := by decide +kernel
private theorem c247680 : checkChunk 247680 128 = true := by decide +kernel
private theorem c247808 : checkChunk 247808 128 = true := by decide +kernel
private theorem c247936 : checkChunk 247936 128 = true := by decide +kernel
private theorem c248064 : checkChunk 248064 128 = true := by decide +kernel
private theorem c248192 : checkChunk 248192 128 = true := by decide +kernel
private theorem c248320 : checkChunk 248320 128 = true := by decide +kernel
private theorem c248448 : checkChunk 248448 128 = true := by decide +kernel
private theorem c248576 : checkChunk 248576 128 = true := by decide +kernel
private theorem c248704 : checkChunk 248704 128 = true := by decide +kernel
private theorem c248832 : checkChunk 248832 128 = true := by decide +kernel
private theorem c248960 : checkChunk 248960 128 = true := by decide +kernel
private theorem c249088 : checkChunk 249088 128 = true := by decide +kernel
private theorem c249216 : checkChunk 249216 128 = true := by decide +kernel
private theorem c249344 : checkChunk 249344 128 = true := by decide +kernel
private theorem c249472 : checkChunk 249472 128 = true := by decide +kernel
private theorem c249600 : checkChunk 249600 128 = true := by decide +kernel
private theorem c249728 : checkChunk 249728 128 = true := by decide +kernel
private theorem c249856 : checkChunk 249856 128 = true := by decide +kernel
private theorem c249984 : checkChunk 249984 128 = true := by decide +kernel
private theorem c250112 : checkChunk 250112 128 = true := by decide +kernel
private theorem c250240 : checkChunk 250240 128 = true := by decide +kernel
private theorem c250368 : checkChunk 250368 128 = true := by decide +kernel
private theorem c250496 : checkChunk 250496 128 = true := by decide +kernel
private theorem c250624 : checkChunk 250624 128 = true := by decide +kernel
private theorem c250752 : checkChunk 250752 128 = true := by decide +kernel
private theorem c250880 : checkChunk 250880 128 = true := by decide +kernel
private theorem c251008 : checkChunk 251008 128 = true := by decide +kernel
private theorem c251136 : checkChunk 251136 128 = true := by decide +kernel
private theorem c251264 : checkChunk 251264 128 = true := by decide +kernel
private theorem c251392 : checkChunk 251392 128 = true := by decide +kernel
private theorem c251520 : checkChunk 251520 128 = true := by decide +kernel
private theorem c251648 : checkChunk 251648 128 = true := by decide +kernel
private theorem c251776 : checkChunk 251776 128 = true := by decide +kernel
private theorem c251904 : checkChunk 251904 128 = true := by decide +kernel
private theorem c252032 : checkChunk 252032 128 = true := by decide +kernel
private theorem c252160 : checkChunk 252160 128 = true := by decide +kernel
private theorem c252288 : checkChunk 252288 128 = true := by decide +kernel
private theorem c252416 : checkChunk 252416 128 = true := by decide +kernel
private theorem c252544 : checkChunk 252544 128 = true := by decide +kernel
private theorem c252672 : checkChunk 252672 128 = true := by decide +kernel
private theorem c252800 : checkChunk 252800 128 = true := by decide +kernel
private theorem c252928 : checkChunk 252928 128 = true := by decide +kernel
private theorem c253056 : checkChunk 253056 128 = true := by decide +kernel
private theorem c253184 : checkChunk 253184 128 = true := by decide +kernel
private theorem c253312 : checkChunk 253312 128 = true := by decide +kernel
private theorem c253440 : checkChunk 253440 128 = true := by decide +kernel
private theorem c253568 : checkChunk 253568 128 = true := by decide +kernel
private theorem c253696 : checkChunk 253696 128 = true := by decide +kernel
private theorem c253824 : checkChunk 253824 128 = true := by decide +kernel

public theorem checked : Checked 245760 253952 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 245760 128 c245760) (checkChunk_sound 245888 128 c245888)) (Checked.append (checkChunk_sound 246016 128 c246016) (checkChunk_sound 246144 128 c246144))) (Checked.append (Checked.append (checkChunk_sound 246272 128 c246272) (checkChunk_sound 246400 128 c246400)) (Checked.append (checkChunk_sound 246528 128 c246528) (checkChunk_sound 246656 128 c246656)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 246784 128 c246784) (checkChunk_sound 246912 128 c246912)) (Checked.append (checkChunk_sound 247040 128 c247040) (checkChunk_sound 247168 128 c247168))) (Checked.append (Checked.append (checkChunk_sound 247296 128 c247296) (checkChunk_sound 247424 128 c247424)) (Checked.append (checkChunk_sound 247552 128 c247552) (checkChunk_sound 247680 128 c247680))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 247808 128 c247808) (checkChunk_sound 247936 128 c247936)) (Checked.append (checkChunk_sound 248064 128 c248064) (checkChunk_sound 248192 128 c248192))) (Checked.append (Checked.append (checkChunk_sound 248320 128 c248320) (checkChunk_sound 248448 128 c248448)) (Checked.append (checkChunk_sound 248576 128 c248576) (checkChunk_sound 248704 128 c248704)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 248832 128 c248832) (checkChunk_sound 248960 128 c248960)) (Checked.append (checkChunk_sound 249088 128 c249088) (checkChunk_sound 249216 128 c249216))) (Checked.append (Checked.append (checkChunk_sound 249344 128 c249344) (checkChunk_sound 249472 128 c249472)) (Checked.append (checkChunk_sound 249600 128 c249600) (checkChunk_sound 249728 128 c249728)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 249856 128 c249856) (checkChunk_sound 249984 128 c249984)) (Checked.append (checkChunk_sound 250112 128 c250112) (checkChunk_sound 250240 128 c250240))) (Checked.append (Checked.append (checkChunk_sound 250368 128 c250368) (checkChunk_sound 250496 128 c250496)) (Checked.append (checkChunk_sound 250624 128 c250624) (checkChunk_sound 250752 128 c250752)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 250880 128 c250880) (checkChunk_sound 251008 128 c251008)) (Checked.append (checkChunk_sound 251136 128 c251136) (checkChunk_sound 251264 128 c251264))) (Checked.append (Checked.append (checkChunk_sound 251392 128 c251392) (checkChunk_sound 251520 128 c251520)) (Checked.append (checkChunk_sound 251648 128 c251648) (checkChunk_sound 251776 128 c251776))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 251904 128 c251904) (checkChunk_sound 252032 128 c252032)) (Checked.append (checkChunk_sound 252160 128 c252160) (checkChunk_sound 252288 128 c252288))) (Checked.append (Checked.append (checkChunk_sound 252416 128 c252416) (checkChunk_sound 252544 128 c252544)) (Checked.append (checkChunk_sound 252672 128 c252672) (checkChunk_sound 252800 128 c252800)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 252928 128 c252928) (checkChunk_sound 253056 128 c253056)) (Checked.append (checkChunk_sound 253184 128 c253184) (checkChunk_sound 253312 128 c253312))) (Checked.append (Checked.append (checkChunk_sound 253440 128 c253440) (checkChunk_sound 253568 128 c253568)) (Checked.append (checkChunk_sound 253696 128 c253696) (checkChunk_sound 253824 128 c253824)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B003
