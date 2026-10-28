module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [57344, 65536).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B006
private theorem c57344 : checkChunk 57344 128 = true := by decide +kernel
private theorem c57472 : checkChunk 57472 128 = true := by decide +kernel
private theorem c57600 : checkChunk 57600 128 = true := by decide +kernel
private theorem c57728 : checkChunk 57728 128 = true := by decide +kernel
private theorem c57856 : checkChunk 57856 128 = true := by decide +kernel
private theorem c57984 : checkChunk 57984 128 = true := by decide +kernel
private theorem c58112 : checkChunk 58112 128 = true := by decide +kernel
private theorem c58240 : checkChunk 58240 128 = true := by decide +kernel
private theorem c58368 : checkChunk 58368 128 = true := by decide +kernel
private theorem c58496 : checkChunk 58496 128 = true := by decide +kernel
private theorem c58624 : checkChunk 58624 128 = true := by decide +kernel
private theorem c58752 : checkChunk 58752 128 = true := by decide +kernel
private theorem c58880 : checkChunk 58880 128 = true := by decide +kernel
private theorem c59008 : checkChunk 59008 128 = true := by decide +kernel
private theorem c59136 : checkChunk 59136 128 = true := by decide +kernel
private theorem c59264 : checkChunk 59264 128 = true := by decide +kernel
private theorem c59392 : checkChunk 59392 128 = true := by decide +kernel
private theorem c59520 : checkChunk 59520 128 = true := by decide +kernel
private theorem c59648 : checkChunk 59648 128 = true := by decide +kernel
private theorem c59776 : checkChunk 59776 128 = true := by decide +kernel
private theorem c59904 : checkChunk 59904 128 = true := by decide +kernel
private theorem c60032 : checkChunk 60032 128 = true := by decide +kernel
private theorem c60160 : checkChunk 60160 128 = true := by decide +kernel
private theorem c60288 : checkChunk 60288 128 = true := by decide +kernel
private theorem c60416 : checkChunk 60416 128 = true := by decide +kernel
private theorem c60544 : checkChunk 60544 128 = true := by decide +kernel
private theorem c60672 : checkChunk 60672 128 = true := by decide +kernel
private theorem c60800 : checkChunk 60800 128 = true := by decide +kernel
private theorem c60928 : checkChunk 60928 128 = true := by decide +kernel
private theorem c61056 : checkChunk 61056 128 = true := by decide +kernel
private theorem c61184 : checkChunk 61184 128 = true := by decide +kernel
private theorem c61312 : checkChunk 61312 128 = true := by decide +kernel
private theorem c61440 : checkChunk 61440 128 = true := by decide +kernel
private theorem c61568 : checkChunk 61568 128 = true := by decide +kernel
private theorem c61696 : checkChunk 61696 128 = true := by decide +kernel
private theorem c61824 : checkChunk 61824 128 = true := by decide +kernel
private theorem c61952 : checkChunk 61952 128 = true := by decide +kernel
private theorem c62080 : checkChunk 62080 128 = true := by decide +kernel
private theorem c62208 : checkChunk 62208 128 = true := by decide +kernel
private theorem c62336 : checkChunk 62336 128 = true := by decide +kernel
private theorem c62464 : checkChunk 62464 128 = true := by decide +kernel
private theorem c62592 : checkChunk 62592 128 = true := by decide +kernel
private theorem c62720 : checkChunk 62720 128 = true := by decide +kernel
private theorem c62848 : checkChunk 62848 128 = true := by decide +kernel
private theorem c62976 : checkChunk 62976 128 = true := by decide +kernel
private theorem c63104 : checkChunk 63104 128 = true := by decide +kernel
private theorem c63232 : checkChunk 63232 128 = true := by decide +kernel
private theorem c63360 : checkChunk 63360 128 = true := by decide +kernel
private theorem c63488 : checkChunk 63488 128 = true := by decide +kernel
private theorem c63616 : checkChunk 63616 128 = true := by decide +kernel
private theorem c63744 : checkChunk 63744 128 = true := by decide +kernel
private theorem c63872 : checkChunk 63872 128 = true := by decide +kernel
private theorem c64000 : checkChunk 64000 128 = true := by decide +kernel
private theorem c64128 : checkChunk 64128 128 = true := by decide +kernel
private theorem c64256 : checkChunk 64256 128 = true := by decide +kernel
private theorem c64384 : checkChunk 64384 128 = true := by decide +kernel
private theorem c64512 : checkChunk 64512 128 = true := by decide +kernel
private theorem c64640 : checkChunk 64640 128 = true := by decide +kernel
private theorem c64768 : checkChunk 64768 128 = true := by decide +kernel
private theorem c64896 : checkChunk 64896 128 = true := by decide +kernel
private theorem c65024 : checkChunk 65024 128 = true := by decide +kernel
private theorem c65152 : checkChunk 65152 128 = true := by decide +kernel
private theorem c65280 : checkChunk 65280 128 = true := by decide +kernel
private theorem c65408 : checkChunk 65408 128 = true := by decide +kernel

public theorem checked : Checked 57344 65536 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 57344 128 c57344) (checkChunk_sound 57472 128 c57472)) (Checked.append (checkChunk_sound 57600 128 c57600) (checkChunk_sound 57728 128 c57728))) (Checked.append (Checked.append (checkChunk_sound 57856 128 c57856) (checkChunk_sound 57984 128 c57984)) (Checked.append (checkChunk_sound 58112 128 c58112) (checkChunk_sound 58240 128 c58240)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 58368 128 c58368) (checkChunk_sound 58496 128 c58496)) (Checked.append (checkChunk_sound 58624 128 c58624) (checkChunk_sound 58752 128 c58752))) (Checked.append (Checked.append (checkChunk_sound 58880 128 c58880) (checkChunk_sound 59008 128 c59008)) (Checked.append (checkChunk_sound 59136 128 c59136) (checkChunk_sound 59264 128 c59264))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 59392 128 c59392) (checkChunk_sound 59520 128 c59520)) (Checked.append (checkChunk_sound 59648 128 c59648) (checkChunk_sound 59776 128 c59776))) (Checked.append (Checked.append (checkChunk_sound 59904 128 c59904) (checkChunk_sound 60032 128 c60032)) (Checked.append (checkChunk_sound 60160 128 c60160) (checkChunk_sound 60288 128 c60288)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 60416 128 c60416) (checkChunk_sound 60544 128 c60544)) (Checked.append (checkChunk_sound 60672 128 c60672) (checkChunk_sound 60800 128 c60800))) (Checked.append (Checked.append (checkChunk_sound 60928 128 c60928) (checkChunk_sound 61056 128 c61056)) (Checked.append (checkChunk_sound 61184 128 c61184) (checkChunk_sound 61312 128 c61312)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 61440 128 c61440) (checkChunk_sound 61568 128 c61568)) (Checked.append (checkChunk_sound 61696 128 c61696) (checkChunk_sound 61824 128 c61824))) (Checked.append (Checked.append (checkChunk_sound 61952 128 c61952) (checkChunk_sound 62080 128 c62080)) (Checked.append (checkChunk_sound 62208 128 c62208) (checkChunk_sound 62336 128 c62336)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 62464 128 c62464) (checkChunk_sound 62592 128 c62592)) (Checked.append (checkChunk_sound 62720 128 c62720) (checkChunk_sound 62848 128 c62848))) (Checked.append (Checked.append (checkChunk_sound 62976 128 c62976) (checkChunk_sound 63104 128 c63104)) (Checked.append (checkChunk_sound 63232 128 c63232) (checkChunk_sound 63360 128 c63360))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 63488 128 c63488) (checkChunk_sound 63616 128 c63616)) (Checked.append (checkChunk_sound 63744 128 c63744) (checkChunk_sound 63872 128 c63872))) (Checked.append (Checked.append (checkChunk_sound 64000 128 c64000) (checkChunk_sound 64128 128 c64128)) (Checked.append (checkChunk_sound 64256 128 c64256) (checkChunk_sound 64384 128 c64384)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 64512 128 c64512) (checkChunk_sound 64640 128 c64640)) (Checked.append (checkChunk_sound 64768 128 c64768) (checkChunk_sound 64896 128 c64896))) (Checked.append (Checked.append (checkChunk_sound 65024 128 c65024) (checkChunk_sound 65152 128 c65152)) (Checked.append (checkChunk_sound 65280 128 c65280) (checkChunk_sound 65408 128 c65408)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B006
