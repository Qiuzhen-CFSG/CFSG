module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [262144, 270336).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B005
private theorem c262144 : checkChunk 262144 128 = true := by decide +kernel
private theorem c262272 : checkChunk 262272 128 = true := by decide +kernel
private theorem c262400 : checkChunk 262400 128 = true := by decide +kernel
private theorem c262528 : checkChunk 262528 128 = true := by decide +kernel
private theorem c262656 : checkChunk 262656 128 = true := by decide +kernel
private theorem c262784 : checkChunk 262784 128 = true := by decide +kernel
private theorem c262912 : checkChunk 262912 128 = true := by decide +kernel
private theorem c263040 : checkChunk 263040 128 = true := by decide +kernel
private theorem c263168 : checkChunk 263168 128 = true := by decide +kernel
private theorem c263296 : checkChunk 263296 128 = true := by decide +kernel
private theorem c263424 : checkChunk 263424 128 = true := by decide +kernel
private theorem c263552 : checkChunk 263552 128 = true := by decide +kernel
private theorem c263680 : checkChunk 263680 128 = true := by decide +kernel
private theorem c263808 : checkChunk 263808 128 = true := by decide +kernel
private theorem c263936 : checkChunk 263936 128 = true := by decide +kernel
private theorem c264064 : checkChunk 264064 128 = true := by decide +kernel
private theorem c264192 : checkChunk 264192 128 = true := by decide +kernel
private theorem c264320 : checkChunk 264320 128 = true := by decide +kernel
private theorem c264448 : checkChunk 264448 128 = true := by decide +kernel
private theorem c264576 : checkChunk 264576 128 = true := by decide +kernel
private theorem c264704 : checkChunk 264704 128 = true := by decide +kernel
private theorem c264832 : checkChunk 264832 128 = true := by decide +kernel
private theorem c264960 : checkChunk 264960 128 = true := by decide +kernel
private theorem c265088 : checkChunk 265088 128 = true := by decide +kernel
private theorem c265216 : checkChunk 265216 128 = true := by decide +kernel
private theorem c265344 : checkChunk 265344 128 = true := by decide +kernel
private theorem c265472 : checkChunk 265472 128 = true := by decide +kernel
private theorem c265600 : checkChunk 265600 128 = true := by decide +kernel
private theorem c265728 : checkChunk 265728 128 = true := by decide +kernel
private theorem c265856 : checkChunk 265856 128 = true := by decide +kernel
private theorem c265984 : checkChunk 265984 128 = true := by decide +kernel
private theorem c266112 : checkChunk 266112 128 = true := by decide +kernel
private theorem c266240 : checkChunk 266240 128 = true := by decide +kernel
private theorem c266368 : checkChunk 266368 128 = true := by decide +kernel
private theorem c266496 : checkChunk 266496 128 = true := by decide +kernel
private theorem c266624 : checkChunk 266624 128 = true := by decide +kernel
private theorem c266752 : checkChunk 266752 128 = true := by decide +kernel
private theorem c266880 : checkChunk 266880 128 = true := by decide +kernel
private theorem c267008 : checkChunk 267008 128 = true := by decide +kernel
private theorem c267136 : checkChunk 267136 128 = true := by decide +kernel
private theorem c267264 : checkChunk 267264 128 = true := by decide +kernel
private theorem c267392 : checkChunk 267392 128 = true := by decide +kernel
private theorem c267520 : checkChunk 267520 128 = true := by decide +kernel
private theorem c267648 : checkChunk 267648 128 = true := by decide +kernel
private theorem c267776 : checkChunk 267776 128 = true := by decide +kernel
private theorem c267904 : checkChunk 267904 128 = true := by decide +kernel
private theorem c268032 : checkChunk 268032 128 = true := by decide +kernel
private theorem c268160 : checkChunk 268160 128 = true := by decide +kernel
private theorem c268288 : checkChunk 268288 128 = true := by decide +kernel
private theorem c268416 : checkChunk 268416 128 = true := by decide +kernel
private theorem c268544 : checkChunk 268544 128 = true := by decide +kernel
private theorem c268672 : checkChunk 268672 128 = true := by decide +kernel
private theorem c268800 : checkChunk 268800 128 = true := by decide +kernel
private theorem c268928 : checkChunk 268928 128 = true := by decide +kernel
private theorem c269056 : checkChunk 269056 128 = true := by decide +kernel
private theorem c269184 : checkChunk 269184 128 = true := by decide +kernel
private theorem c269312 : checkChunk 269312 128 = true := by decide +kernel
private theorem c269440 : checkChunk 269440 128 = true := by decide +kernel
private theorem c269568 : checkChunk 269568 128 = true := by decide +kernel
private theorem c269696 : checkChunk 269696 128 = true := by decide +kernel
private theorem c269824 : checkChunk 269824 128 = true := by decide +kernel
private theorem c269952 : checkChunk 269952 128 = true := by decide +kernel
private theorem c270080 : checkChunk 270080 128 = true := by decide +kernel
private theorem c270208 : checkChunk 270208 128 = true := by decide +kernel

public theorem checked : Checked 262144 270336 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 262144 128 c262144) (checkChunk_sound 262272 128 c262272)) (Checked.append (checkChunk_sound 262400 128 c262400) (checkChunk_sound 262528 128 c262528))) (Checked.append (Checked.append (checkChunk_sound 262656 128 c262656) (checkChunk_sound 262784 128 c262784)) (Checked.append (checkChunk_sound 262912 128 c262912) (checkChunk_sound 263040 128 c263040)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 263168 128 c263168) (checkChunk_sound 263296 128 c263296)) (Checked.append (checkChunk_sound 263424 128 c263424) (checkChunk_sound 263552 128 c263552))) (Checked.append (Checked.append (checkChunk_sound 263680 128 c263680) (checkChunk_sound 263808 128 c263808)) (Checked.append (checkChunk_sound 263936 128 c263936) (checkChunk_sound 264064 128 c264064))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 264192 128 c264192) (checkChunk_sound 264320 128 c264320)) (Checked.append (checkChunk_sound 264448 128 c264448) (checkChunk_sound 264576 128 c264576))) (Checked.append (Checked.append (checkChunk_sound 264704 128 c264704) (checkChunk_sound 264832 128 c264832)) (Checked.append (checkChunk_sound 264960 128 c264960) (checkChunk_sound 265088 128 c265088)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 265216 128 c265216) (checkChunk_sound 265344 128 c265344)) (Checked.append (checkChunk_sound 265472 128 c265472) (checkChunk_sound 265600 128 c265600))) (Checked.append (Checked.append (checkChunk_sound 265728 128 c265728) (checkChunk_sound 265856 128 c265856)) (Checked.append (checkChunk_sound 265984 128 c265984) (checkChunk_sound 266112 128 c266112)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 266240 128 c266240) (checkChunk_sound 266368 128 c266368)) (Checked.append (checkChunk_sound 266496 128 c266496) (checkChunk_sound 266624 128 c266624))) (Checked.append (Checked.append (checkChunk_sound 266752 128 c266752) (checkChunk_sound 266880 128 c266880)) (Checked.append (checkChunk_sound 267008 128 c267008) (checkChunk_sound 267136 128 c267136)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 267264 128 c267264) (checkChunk_sound 267392 128 c267392)) (Checked.append (checkChunk_sound 267520 128 c267520) (checkChunk_sound 267648 128 c267648))) (Checked.append (Checked.append (checkChunk_sound 267776 128 c267776) (checkChunk_sound 267904 128 c267904)) (Checked.append (checkChunk_sound 268032 128 c268032) (checkChunk_sound 268160 128 c268160))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 268288 128 c268288) (checkChunk_sound 268416 128 c268416)) (Checked.append (checkChunk_sound 268544 128 c268544) (checkChunk_sound 268672 128 c268672))) (Checked.append (Checked.append (checkChunk_sound 268800 128 c268800) (checkChunk_sound 268928 128 c268928)) (Checked.append (checkChunk_sound 269056 128 c269056) (checkChunk_sound 269184 128 c269184)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 269312 128 c269312) (checkChunk_sound 269440 128 c269440)) (Checked.append (checkChunk_sound 269568 128 c269568) (checkChunk_sound 269696 128 c269696))) (Checked.append (Checked.append (checkChunk_sound 269824 128 c269824) (checkChunk_sound 269952 128 c269952)) (Checked.append (checkChunk_sound 270080 128 c270080) (checkChunk_sound 270208 128 c270208)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B005
