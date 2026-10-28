module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [8192, 16384).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B000
private theorem c8192 : checkChunk 8192 128 = true := by decide +kernel
private theorem c8320 : checkChunk 8320 128 = true := by decide +kernel
private theorem c8448 : checkChunk 8448 128 = true := by decide +kernel
private theorem c8576 : checkChunk 8576 128 = true := by decide +kernel
private theorem c8704 : checkChunk 8704 128 = true := by decide +kernel
private theorem c8832 : checkChunk 8832 128 = true := by decide +kernel
private theorem c8960 : checkChunk 8960 128 = true := by decide +kernel
private theorem c9088 : checkChunk 9088 128 = true := by decide +kernel
private theorem c9216 : checkChunk 9216 128 = true := by decide +kernel
private theorem c9344 : checkChunk 9344 128 = true := by decide +kernel
private theorem c9472 : checkChunk 9472 128 = true := by decide +kernel
private theorem c9600 : checkChunk 9600 128 = true := by decide +kernel
private theorem c9728 : checkChunk 9728 128 = true := by decide +kernel
private theorem c9856 : checkChunk 9856 128 = true := by decide +kernel
private theorem c9984 : checkChunk 9984 128 = true := by decide +kernel
private theorem c10112 : checkChunk 10112 128 = true := by decide +kernel
private theorem c10240 : checkChunk 10240 128 = true := by decide +kernel
private theorem c10368 : checkChunk 10368 128 = true := by decide +kernel
private theorem c10496 : checkChunk 10496 128 = true := by decide +kernel
private theorem c10624 : checkChunk 10624 128 = true := by decide +kernel
private theorem c10752 : checkChunk 10752 128 = true := by decide +kernel
private theorem c10880 : checkChunk 10880 128 = true := by decide +kernel
private theorem c11008 : checkChunk 11008 128 = true := by decide +kernel
private theorem c11136 : checkChunk 11136 128 = true := by decide +kernel
private theorem c11264 : checkChunk 11264 128 = true := by decide +kernel
private theorem c11392 : checkChunk 11392 128 = true := by decide +kernel
private theorem c11520 : checkChunk 11520 128 = true := by decide +kernel
private theorem c11648 : checkChunk 11648 128 = true := by decide +kernel
private theorem c11776 : checkChunk 11776 128 = true := by decide +kernel
private theorem c11904 : checkChunk 11904 128 = true := by decide +kernel
private theorem c12032 : checkChunk 12032 128 = true := by decide +kernel
private theorem c12160 : checkChunk 12160 128 = true := by decide +kernel
private theorem c12288 : checkChunk 12288 128 = true := by decide +kernel
private theorem c12416 : checkChunk 12416 128 = true := by decide +kernel
private theorem c12544 : checkChunk 12544 128 = true := by decide +kernel
private theorem c12672 : checkChunk 12672 128 = true := by decide +kernel
private theorem c12800 : checkChunk 12800 128 = true := by decide +kernel
private theorem c12928 : checkChunk 12928 128 = true := by decide +kernel
private theorem c13056 : checkChunk 13056 128 = true := by decide +kernel
private theorem c13184 : checkChunk 13184 128 = true := by decide +kernel
private theorem c13312 : checkChunk 13312 128 = true := by decide +kernel
private theorem c13440 : checkChunk 13440 128 = true := by decide +kernel
private theorem c13568 : checkChunk 13568 128 = true := by decide +kernel
private theorem c13696 : checkChunk 13696 128 = true := by decide +kernel
private theorem c13824 : checkChunk 13824 128 = true := by decide +kernel
private theorem c13952 : checkChunk 13952 128 = true := by decide +kernel
private theorem c14080 : checkChunk 14080 128 = true := by decide +kernel
private theorem c14208 : checkChunk 14208 128 = true := by decide +kernel
private theorem c14336 : checkChunk 14336 128 = true := by decide +kernel
private theorem c14464 : checkChunk 14464 128 = true := by decide +kernel
private theorem c14592 : checkChunk 14592 128 = true := by decide +kernel
private theorem c14720 : checkChunk 14720 128 = true := by decide +kernel
private theorem c14848 : checkChunk 14848 128 = true := by decide +kernel
private theorem c14976 : checkChunk 14976 128 = true := by decide +kernel
private theorem c15104 : checkChunk 15104 128 = true := by decide +kernel
private theorem c15232 : checkChunk 15232 128 = true := by decide +kernel
private theorem c15360 : checkChunk 15360 128 = true := by decide +kernel
private theorem c15488 : checkChunk 15488 128 = true := by decide +kernel
private theorem c15616 : checkChunk 15616 128 = true := by decide +kernel
private theorem c15744 : checkChunk 15744 128 = true := by decide +kernel
private theorem c15872 : checkChunk 15872 128 = true := by decide +kernel
private theorem c16000 : checkChunk 16000 128 = true := by decide +kernel
private theorem c16128 : checkChunk 16128 128 = true := by decide +kernel
private theorem c16256 : checkChunk 16256 128 = true := by decide +kernel

public theorem checked : Checked 8192 16384 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 8192 128 c8192) (checkChunk_sound 8320 128 c8320)) (Checked.append (checkChunk_sound 8448 128 c8448) (checkChunk_sound 8576 128 c8576))) (Checked.append (Checked.append (checkChunk_sound 8704 128 c8704) (checkChunk_sound 8832 128 c8832)) (Checked.append (checkChunk_sound 8960 128 c8960) (checkChunk_sound 9088 128 c9088)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 9216 128 c9216) (checkChunk_sound 9344 128 c9344)) (Checked.append (checkChunk_sound 9472 128 c9472) (checkChunk_sound 9600 128 c9600))) (Checked.append (Checked.append (checkChunk_sound 9728 128 c9728) (checkChunk_sound 9856 128 c9856)) (Checked.append (checkChunk_sound 9984 128 c9984) (checkChunk_sound 10112 128 c10112))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 10240 128 c10240) (checkChunk_sound 10368 128 c10368)) (Checked.append (checkChunk_sound 10496 128 c10496) (checkChunk_sound 10624 128 c10624))) (Checked.append (Checked.append (checkChunk_sound 10752 128 c10752) (checkChunk_sound 10880 128 c10880)) (Checked.append (checkChunk_sound 11008 128 c11008) (checkChunk_sound 11136 128 c11136)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 11264 128 c11264) (checkChunk_sound 11392 128 c11392)) (Checked.append (checkChunk_sound 11520 128 c11520) (checkChunk_sound 11648 128 c11648))) (Checked.append (Checked.append (checkChunk_sound 11776 128 c11776) (checkChunk_sound 11904 128 c11904)) (Checked.append (checkChunk_sound 12032 128 c12032) (checkChunk_sound 12160 128 c12160)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 12288 128 c12288) (checkChunk_sound 12416 128 c12416)) (Checked.append (checkChunk_sound 12544 128 c12544) (checkChunk_sound 12672 128 c12672))) (Checked.append (Checked.append (checkChunk_sound 12800 128 c12800) (checkChunk_sound 12928 128 c12928)) (Checked.append (checkChunk_sound 13056 128 c13056) (checkChunk_sound 13184 128 c13184)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 13312 128 c13312) (checkChunk_sound 13440 128 c13440)) (Checked.append (checkChunk_sound 13568 128 c13568) (checkChunk_sound 13696 128 c13696))) (Checked.append (Checked.append (checkChunk_sound 13824 128 c13824) (checkChunk_sound 13952 128 c13952)) (Checked.append (checkChunk_sound 14080 128 c14080) (checkChunk_sound 14208 128 c14208))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 14336 128 c14336) (checkChunk_sound 14464 128 c14464)) (Checked.append (checkChunk_sound 14592 128 c14592) (checkChunk_sound 14720 128 c14720))) (Checked.append (Checked.append (checkChunk_sound 14848 128 c14848) (checkChunk_sound 14976 128 c14976)) (Checked.append (checkChunk_sound 15104 128 c15104) (checkChunk_sound 15232 128 c15232)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 15360 128 c15360) (checkChunk_sound 15488 128 c15488)) (Checked.append (checkChunk_sound 15616 128 c15616) (checkChunk_sound 15744 128 c15744))) (Checked.append (Checked.append (checkChunk_sound 15872 128 c15872) (checkChunk_sound 16000 128 c16000)) (Checked.append (checkChunk_sound 16128 128 c16128) (checkChunk_sound 16256 128 c16256)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00.B000
