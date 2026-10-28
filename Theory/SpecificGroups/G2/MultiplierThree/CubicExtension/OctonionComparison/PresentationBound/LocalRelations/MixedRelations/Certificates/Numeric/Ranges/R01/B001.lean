module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [229376, 237568).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B001
private theorem c229376 : checkChunk 229376 128 = true := by decide +kernel
private theorem c229504 : checkChunk 229504 128 = true := by decide +kernel
private theorem c229632 : checkChunk 229632 128 = true := by decide +kernel
private theorem c229760 : checkChunk 229760 128 = true := by decide +kernel
private theorem c229888 : checkChunk 229888 128 = true := by decide +kernel
private theorem c230016 : checkChunk 230016 128 = true := by decide +kernel
private theorem c230144 : checkChunk 230144 128 = true := by decide +kernel
private theorem c230272 : checkChunk 230272 128 = true := by decide +kernel
private theorem c230400 : checkChunk 230400 128 = true := by decide +kernel
private theorem c230528 : checkChunk 230528 128 = true := by decide +kernel
private theorem c230656 : checkChunk 230656 128 = true := by decide +kernel
private theorem c230784 : checkChunk 230784 128 = true := by decide +kernel
private theorem c230912 : checkChunk 230912 128 = true := by decide +kernel
private theorem c231040 : checkChunk 231040 128 = true := by decide +kernel
private theorem c231168 : checkChunk 231168 128 = true := by decide +kernel
private theorem c231296 : checkChunk 231296 128 = true := by decide +kernel
private theorem c231424 : checkChunk 231424 128 = true := by decide +kernel
private theorem c231552 : checkChunk 231552 128 = true := by decide +kernel
private theorem c231680 : checkChunk 231680 128 = true := by decide +kernel
private theorem c231808 : checkChunk 231808 128 = true := by decide +kernel
private theorem c231936 : checkChunk 231936 128 = true := by decide +kernel
private theorem c232064 : checkChunk 232064 128 = true := by decide +kernel
private theorem c232192 : checkChunk 232192 128 = true := by decide +kernel
private theorem c232320 : checkChunk 232320 128 = true := by decide +kernel
private theorem c232448 : checkChunk 232448 128 = true := by decide +kernel
private theorem c232576 : checkChunk 232576 128 = true := by decide +kernel
private theorem c232704 : checkChunk 232704 128 = true := by decide +kernel
private theorem c232832 : checkChunk 232832 128 = true := by decide +kernel
private theorem c232960 : checkChunk 232960 128 = true := by decide +kernel
private theorem c233088 : checkChunk 233088 128 = true := by decide +kernel
private theorem c233216 : checkChunk 233216 128 = true := by decide +kernel
private theorem c233344 : checkChunk 233344 128 = true := by decide +kernel
private theorem c233472 : checkChunk 233472 128 = true := by decide +kernel
private theorem c233600 : checkChunk 233600 128 = true := by decide +kernel
private theorem c233728 : checkChunk 233728 128 = true := by decide +kernel
private theorem c233856 : checkChunk 233856 128 = true := by decide +kernel
private theorem c233984 : checkChunk 233984 128 = true := by decide +kernel
private theorem c234112 : checkChunk 234112 128 = true := by decide +kernel
private theorem c234240 : checkChunk 234240 128 = true := by decide +kernel
private theorem c234368 : checkChunk 234368 128 = true := by decide +kernel
private theorem c234496 : checkChunk 234496 128 = true := by decide +kernel
private theorem c234624 : checkChunk 234624 128 = true := by decide +kernel
private theorem c234752 : checkChunk 234752 128 = true := by decide +kernel
private theorem c234880 : checkChunk 234880 128 = true := by decide +kernel
private theorem c235008 : checkChunk 235008 128 = true := by decide +kernel
private theorem c235136 : checkChunk 235136 128 = true := by decide +kernel
private theorem c235264 : checkChunk 235264 128 = true := by decide +kernel
private theorem c235392 : checkChunk 235392 128 = true := by decide +kernel
private theorem c235520 : checkChunk 235520 128 = true := by decide +kernel
private theorem c235648 : checkChunk 235648 128 = true := by decide +kernel
private theorem c235776 : checkChunk 235776 128 = true := by decide +kernel
private theorem c235904 : checkChunk 235904 128 = true := by decide +kernel
private theorem c236032 : checkChunk 236032 128 = true := by decide +kernel
private theorem c236160 : checkChunk 236160 128 = true := by decide +kernel
private theorem c236288 : checkChunk 236288 128 = true := by decide +kernel
private theorem c236416 : checkChunk 236416 128 = true := by decide +kernel
private theorem c236544 : checkChunk 236544 128 = true := by decide +kernel
private theorem c236672 : checkChunk 236672 128 = true := by decide +kernel
private theorem c236800 : checkChunk 236800 128 = true := by decide +kernel
private theorem c236928 : checkChunk 236928 128 = true := by decide +kernel
private theorem c237056 : checkChunk 237056 128 = true := by decide +kernel
private theorem c237184 : checkChunk 237184 128 = true := by decide +kernel
private theorem c237312 : checkChunk 237312 128 = true := by decide +kernel
private theorem c237440 : checkChunk 237440 128 = true := by decide +kernel

public theorem checked : Checked 229376 237568 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 229376 128 c229376) (checkChunk_sound 229504 128 c229504)) (Checked.append (checkChunk_sound 229632 128 c229632) (checkChunk_sound 229760 128 c229760))) (Checked.append (Checked.append (checkChunk_sound 229888 128 c229888) (checkChunk_sound 230016 128 c230016)) (Checked.append (checkChunk_sound 230144 128 c230144) (checkChunk_sound 230272 128 c230272)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 230400 128 c230400) (checkChunk_sound 230528 128 c230528)) (Checked.append (checkChunk_sound 230656 128 c230656) (checkChunk_sound 230784 128 c230784))) (Checked.append (Checked.append (checkChunk_sound 230912 128 c230912) (checkChunk_sound 231040 128 c231040)) (Checked.append (checkChunk_sound 231168 128 c231168) (checkChunk_sound 231296 128 c231296))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 231424 128 c231424) (checkChunk_sound 231552 128 c231552)) (Checked.append (checkChunk_sound 231680 128 c231680) (checkChunk_sound 231808 128 c231808))) (Checked.append (Checked.append (checkChunk_sound 231936 128 c231936) (checkChunk_sound 232064 128 c232064)) (Checked.append (checkChunk_sound 232192 128 c232192) (checkChunk_sound 232320 128 c232320)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 232448 128 c232448) (checkChunk_sound 232576 128 c232576)) (Checked.append (checkChunk_sound 232704 128 c232704) (checkChunk_sound 232832 128 c232832))) (Checked.append (Checked.append (checkChunk_sound 232960 128 c232960) (checkChunk_sound 233088 128 c233088)) (Checked.append (checkChunk_sound 233216 128 c233216) (checkChunk_sound 233344 128 c233344)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 233472 128 c233472) (checkChunk_sound 233600 128 c233600)) (Checked.append (checkChunk_sound 233728 128 c233728) (checkChunk_sound 233856 128 c233856))) (Checked.append (Checked.append (checkChunk_sound 233984 128 c233984) (checkChunk_sound 234112 128 c234112)) (Checked.append (checkChunk_sound 234240 128 c234240) (checkChunk_sound 234368 128 c234368)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 234496 128 c234496) (checkChunk_sound 234624 128 c234624)) (Checked.append (checkChunk_sound 234752 128 c234752) (checkChunk_sound 234880 128 c234880))) (Checked.append (Checked.append (checkChunk_sound 235008 128 c235008) (checkChunk_sound 235136 128 c235136)) (Checked.append (checkChunk_sound 235264 128 c235264) (checkChunk_sound 235392 128 c235392))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 235520 128 c235520) (checkChunk_sound 235648 128 c235648)) (Checked.append (checkChunk_sound 235776 128 c235776) (checkChunk_sound 235904 128 c235904))) (Checked.append (Checked.append (checkChunk_sound 236032 128 c236032) (checkChunk_sound 236160 128 c236160)) (Checked.append (checkChunk_sound 236288 128 c236288) (checkChunk_sound 236416 128 c236416)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 236544 128 c236544) (checkChunk_sound 236672 128 c236672)) (Checked.append (checkChunk_sound 236800 128 c236800) (checkChunk_sound 236928 128 c236928))) (Checked.append (Checked.append (checkChunk_sound 237056 128 c237056) (checkChunk_sound 237184 128 c237184)) (Checked.append (checkChunk_sound 237312 128 c237312) (checkChunk_sound 237440 128 c237440)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B001
