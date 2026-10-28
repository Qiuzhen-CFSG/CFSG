module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [311296, 319488).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B011
private theorem c311296 : checkChunk 311296 128 = true := by decide +kernel
private theorem c311424 : checkChunk 311424 128 = true := by decide +kernel
private theorem c311552 : checkChunk 311552 128 = true := by decide +kernel
private theorem c311680 : checkChunk 311680 128 = true := by decide +kernel
private theorem c311808 : checkChunk 311808 128 = true := by decide +kernel
private theorem c311936 : checkChunk 311936 128 = true := by decide +kernel
private theorem c312064 : checkChunk 312064 128 = true := by decide +kernel
private theorem c312192 : checkChunk 312192 128 = true := by decide +kernel
private theorem c312320 : checkChunk 312320 128 = true := by decide +kernel
private theorem c312448 : checkChunk 312448 128 = true := by decide +kernel
private theorem c312576 : checkChunk 312576 128 = true := by decide +kernel
private theorem c312704 : checkChunk 312704 128 = true := by decide +kernel
private theorem c312832 : checkChunk 312832 128 = true := by decide +kernel
private theorem c312960 : checkChunk 312960 128 = true := by decide +kernel
private theorem c313088 : checkChunk 313088 128 = true := by decide +kernel
private theorem c313216 : checkChunk 313216 128 = true := by decide +kernel
private theorem c313344 : checkChunk 313344 128 = true := by decide +kernel
private theorem c313472 : checkChunk 313472 128 = true := by decide +kernel
private theorem c313600 : checkChunk 313600 128 = true := by decide +kernel
private theorem c313728 : checkChunk 313728 128 = true := by decide +kernel
private theorem c313856 : checkChunk 313856 128 = true := by decide +kernel
private theorem c313984 : checkChunk 313984 128 = true := by decide +kernel
private theorem c314112 : checkChunk 314112 128 = true := by decide +kernel
private theorem c314240 : checkChunk 314240 128 = true := by decide +kernel
private theorem c314368 : checkChunk 314368 128 = true := by decide +kernel
private theorem c314496 : checkChunk 314496 128 = true := by decide +kernel
private theorem c314624 : checkChunk 314624 128 = true := by decide +kernel
private theorem c314752 : checkChunk 314752 128 = true := by decide +kernel
private theorem c314880 : checkChunk 314880 128 = true := by decide +kernel
private theorem c315008 : checkChunk 315008 128 = true := by decide +kernel
private theorem c315136 : checkChunk 315136 128 = true := by decide +kernel
private theorem c315264 : checkChunk 315264 128 = true := by decide +kernel
private theorem c315392 : checkChunk 315392 128 = true := by decide +kernel
private theorem c315520 : checkChunk 315520 128 = true := by decide +kernel
private theorem c315648 : checkChunk 315648 128 = true := by decide +kernel
private theorem c315776 : checkChunk 315776 128 = true := by decide +kernel
private theorem c315904 : checkChunk 315904 128 = true := by decide +kernel
private theorem c316032 : checkChunk 316032 128 = true := by decide +kernel
private theorem c316160 : checkChunk 316160 128 = true := by decide +kernel
private theorem c316288 : checkChunk 316288 128 = true := by decide +kernel
private theorem c316416 : checkChunk 316416 128 = true := by decide +kernel
private theorem c316544 : checkChunk 316544 128 = true := by decide +kernel
private theorem c316672 : checkChunk 316672 128 = true := by decide +kernel
private theorem c316800 : checkChunk 316800 128 = true := by decide +kernel
private theorem c316928 : checkChunk 316928 128 = true := by decide +kernel
private theorem c317056 : checkChunk 317056 128 = true := by decide +kernel
private theorem c317184 : checkChunk 317184 128 = true := by decide +kernel
private theorem c317312 : checkChunk 317312 128 = true := by decide +kernel
private theorem c317440 : checkChunk 317440 128 = true := by decide +kernel
private theorem c317568 : checkChunk 317568 128 = true := by decide +kernel
private theorem c317696 : checkChunk 317696 128 = true := by decide +kernel
private theorem c317824 : checkChunk 317824 128 = true := by decide +kernel
private theorem c317952 : checkChunk 317952 128 = true := by decide +kernel
private theorem c318080 : checkChunk 318080 128 = true := by decide +kernel
private theorem c318208 : checkChunk 318208 128 = true := by decide +kernel
private theorem c318336 : checkChunk 318336 128 = true := by decide +kernel
private theorem c318464 : checkChunk 318464 128 = true := by decide +kernel
private theorem c318592 : checkChunk 318592 128 = true := by decide +kernel
private theorem c318720 : checkChunk 318720 128 = true := by decide +kernel
private theorem c318848 : checkChunk 318848 128 = true := by decide +kernel
private theorem c318976 : checkChunk 318976 128 = true := by decide +kernel
private theorem c319104 : checkChunk 319104 128 = true := by decide +kernel
private theorem c319232 : checkChunk 319232 128 = true := by decide +kernel
private theorem c319360 : checkChunk 319360 128 = true := by decide +kernel

public theorem checked : Checked 311296 319488 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 311296 128 c311296) (checkChunk_sound 311424 128 c311424)) (Checked.append (checkChunk_sound 311552 128 c311552) (checkChunk_sound 311680 128 c311680))) (Checked.append (Checked.append (checkChunk_sound 311808 128 c311808) (checkChunk_sound 311936 128 c311936)) (Checked.append (checkChunk_sound 312064 128 c312064) (checkChunk_sound 312192 128 c312192)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 312320 128 c312320) (checkChunk_sound 312448 128 c312448)) (Checked.append (checkChunk_sound 312576 128 c312576) (checkChunk_sound 312704 128 c312704))) (Checked.append (Checked.append (checkChunk_sound 312832 128 c312832) (checkChunk_sound 312960 128 c312960)) (Checked.append (checkChunk_sound 313088 128 c313088) (checkChunk_sound 313216 128 c313216))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 313344 128 c313344) (checkChunk_sound 313472 128 c313472)) (Checked.append (checkChunk_sound 313600 128 c313600) (checkChunk_sound 313728 128 c313728))) (Checked.append (Checked.append (checkChunk_sound 313856 128 c313856) (checkChunk_sound 313984 128 c313984)) (Checked.append (checkChunk_sound 314112 128 c314112) (checkChunk_sound 314240 128 c314240)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 314368 128 c314368) (checkChunk_sound 314496 128 c314496)) (Checked.append (checkChunk_sound 314624 128 c314624) (checkChunk_sound 314752 128 c314752))) (Checked.append (Checked.append (checkChunk_sound 314880 128 c314880) (checkChunk_sound 315008 128 c315008)) (Checked.append (checkChunk_sound 315136 128 c315136) (checkChunk_sound 315264 128 c315264)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 315392 128 c315392) (checkChunk_sound 315520 128 c315520)) (Checked.append (checkChunk_sound 315648 128 c315648) (checkChunk_sound 315776 128 c315776))) (Checked.append (Checked.append (checkChunk_sound 315904 128 c315904) (checkChunk_sound 316032 128 c316032)) (Checked.append (checkChunk_sound 316160 128 c316160) (checkChunk_sound 316288 128 c316288)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 316416 128 c316416) (checkChunk_sound 316544 128 c316544)) (Checked.append (checkChunk_sound 316672 128 c316672) (checkChunk_sound 316800 128 c316800))) (Checked.append (Checked.append (checkChunk_sound 316928 128 c316928) (checkChunk_sound 317056 128 c317056)) (Checked.append (checkChunk_sound 317184 128 c317184) (checkChunk_sound 317312 128 c317312))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 317440 128 c317440) (checkChunk_sound 317568 128 c317568)) (Checked.append (checkChunk_sound 317696 128 c317696) (checkChunk_sound 317824 128 c317824))) (Checked.append (Checked.append (checkChunk_sound 317952 128 c317952) (checkChunk_sound 318080 128 c318080)) (Checked.append (checkChunk_sound 318208 128 c318208) (checkChunk_sound 318336 128 c318336)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 318464 128 c318464) (checkChunk_sound 318592 128 c318592)) (Checked.append (checkChunk_sound 318720 128 c318720) (checkChunk_sound 318848 128 c318848))) (Checked.append (Checked.append (checkChunk_sound 318976 128 c318976) (checkChunk_sound 319104 128 c319104)) (Checked.append (checkChunk_sound 319232 128 c319232) (checkChunk_sound 319360 128 c319360)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B011
