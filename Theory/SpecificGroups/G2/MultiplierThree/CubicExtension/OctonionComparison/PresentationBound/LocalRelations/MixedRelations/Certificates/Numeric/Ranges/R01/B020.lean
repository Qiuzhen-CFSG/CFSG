module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [385024, 393216).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B020
private theorem c385024 : checkChunk 385024 128 = true := by decide +kernel
private theorem c385152 : checkChunk 385152 128 = true := by decide +kernel
private theorem c385280 : checkChunk 385280 128 = true := by decide +kernel
private theorem c385408 : checkChunk 385408 128 = true := by decide +kernel
private theorem c385536 : checkChunk 385536 128 = true := by decide +kernel
private theorem c385664 : checkChunk 385664 128 = true := by decide +kernel
private theorem c385792 : checkChunk 385792 128 = true := by decide +kernel
private theorem c385920 : checkChunk 385920 128 = true := by decide +kernel
private theorem c386048 : checkChunk 386048 128 = true := by decide +kernel
private theorem c386176 : checkChunk 386176 128 = true := by decide +kernel
private theorem c386304 : checkChunk 386304 128 = true := by decide +kernel
private theorem c386432 : checkChunk 386432 128 = true := by decide +kernel
private theorem c386560 : checkChunk 386560 128 = true := by decide +kernel
private theorem c386688 : checkChunk 386688 128 = true := by decide +kernel
private theorem c386816 : checkChunk 386816 128 = true := by decide +kernel
private theorem c386944 : checkChunk 386944 128 = true := by decide +kernel
private theorem c387072 : checkChunk 387072 128 = true := by decide +kernel
private theorem c387200 : checkChunk 387200 128 = true := by decide +kernel
private theorem c387328 : checkChunk 387328 128 = true := by decide +kernel
private theorem c387456 : checkChunk 387456 128 = true := by decide +kernel
private theorem c387584 : checkChunk 387584 128 = true := by decide +kernel
private theorem c387712 : checkChunk 387712 128 = true := by decide +kernel
private theorem c387840 : checkChunk 387840 128 = true := by decide +kernel
private theorem c387968 : checkChunk 387968 128 = true := by decide +kernel
private theorem c388096 : checkChunk 388096 128 = true := by decide +kernel
private theorem c388224 : checkChunk 388224 128 = true := by decide +kernel
private theorem c388352 : checkChunk 388352 128 = true := by decide +kernel
private theorem c388480 : checkChunk 388480 128 = true := by decide +kernel
private theorem c388608 : checkChunk 388608 128 = true := by decide +kernel
private theorem c388736 : checkChunk 388736 128 = true := by decide +kernel
private theorem c388864 : checkChunk 388864 128 = true := by decide +kernel
private theorem c388992 : checkChunk 388992 128 = true := by decide +kernel
private theorem c389120 : checkChunk 389120 128 = true := by decide +kernel
private theorem c389248 : checkChunk 389248 128 = true := by decide +kernel
private theorem c389376 : checkChunk 389376 128 = true := by decide +kernel
private theorem c389504 : checkChunk 389504 128 = true := by decide +kernel
private theorem c389632 : checkChunk 389632 128 = true := by decide +kernel
private theorem c389760 : checkChunk 389760 128 = true := by decide +kernel
private theorem c389888 : checkChunk 389888 128 = true := by decide +kernel
private theorem c390016 : checkChunk 390016 128 = true := by decide +kernel
private theorem c390144 : checkChunk 390144 128 = true := by decide +kernel
private theorem c390272 : checkChunk 390272 128 = true := by decide +kernel
private theorem c390400 : checkChunk 390400 128 = true := by decide +kernel
private theorem c390528 : checkChunk 390528 128 = true := by decide +kernel
private theorem c390656 : checkChunk 390656 128 = true := by decide +kernel
private theorem c390784 : checkChunk 390784 128 = true := by decide +kernel
private theorem c390912 : checkChunk 390912 128 = true := by decide +kernel
private theorem c391040 : checkChunk 391040 128 = true := by decide +kernel
private theorem c391168 : checkChunk 391168 128 = true := by decide +kernel
private theorem c391296 : checkChunk 391296 128 = true := by decide +kernel
private theorem c391424 : checkChunk 391424 128 = true := by decide +kernel
private theorem c391552 : checkChunk 391552 128 = true := by decide +kernel
private theorem c391680 : checkChunk 391680 128 = true := by decide +kernel
private theorem c391808 : checkChunk 391808 128 = true := by decide +kernel
private theorem c391936 : checkChunk 391936 128 = true := by decide +kernel
private theorem c392064 : checkChunk 392064 128 = true := by decide +kernel
private theorem c392192 : checkChunk 392192 128 = true := by decide +kernel
private theorem c392320 : checkChunk 392320 128 = true := by decide +kernel
private theorem c392448 : checkChunk 392448 128 = true := by decide +kernel
private theorem c392576 : checkChunk 392576 128 = true := by decide +kernel
private theorem c392704 : checkChunk 392704 128 = true := by decide +kernel
private theorem c392832 : checkChunk 392832 128 = true := by decide +kernel
private theorem c392960 : checkChunk 392960 128 = true := by decide +kernel
private theorem c393088 : checkChunk 393088 128 = true := by decide +kernel

public theorem checked : Checked 385024 393216 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 385024 128 c385024) (checkChunk_sound 385152 128 c385152)) (Checked.append (checkChunk_sound 385280 128 c385280) (checkChunk_sound 385408 128 c385408))) (Checked.append (Checked.append (checkChunk_sound 385536 128 c385536) (checkChunk_sound 385664 128 c385664)) (Checked.append (checkChunk_sound 385792 128 c385792) (checkChunk_sound 385920 128 c385920)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 386048 128 c386048) (checkChunk_sound 386176 128 c386176)) (Checked.append (checkChunk_sound 386304 128 c386304) (checkChunk_sound 386432 128 c386432))) (Checked.append (Checked.append (checkChunk_sound 386560 128 c386560) (checkChunk_sound 386688 128 c386688)) (Checked.append (checkChunk_sound 386816 128 c386816) (checkChunk_sound 386944 128 c386944))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 387072 128 c387072) (checkChunk_sound 387200 128 c387200)) (Checked.append (checkChunk_sound 387328 128 c387328) (checkChunk_sound 387456 128 c387456))) (Checked.append (Checked.append (checkChunk_sound 387584 128 c387584) (checkChunk_sound 387712 128 c387712)) (Checked.append (checkChunk_sound 387840 128 c387840) (checkChunk_sound 387968 128 c387968)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 388096 128 c388096) (checkChunk_sound 388224 128 c388224)) (Checked.append (checkChunk_sound 388352 128 c388352) (checkChunk_sound 388480 128 c388480))) (Checked.append (Checked.append (checkChunk_sound 388608 128 c388608) (checkChunk_sound 388736 128 c388736)) (Checked.append (checkChunk_sound 388864 128 c388864) (checkChunk_sound 388992 128 c388992)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 389120 128 c389120) (checkChunk_sound 389248 128 c389248)) (Checked.append (checkChunk_sound 389376 128 c389376) (checkChunk_sound 389504 128 c389504))) (Checked.append (Checked.append (checkChunk_sound 389632 128 c389632) (checkChunk_sound 389760 128 c389760)) (Checked.append (checkChunk_sound 389888 128 c389888) (checkChunk_sound 390016 128 c390016)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 390144 128 c390144) (checkChunk_sound 390272 128 c390272)) (Checked.append (checkChunk_sound 390400 128 c390400) (checkChunk_sound 390528 128 c390528))) (Checked.append (Checked.append (checkChunk_sound 390656 128 c390656) (checkChunk_sound 390784 128 c390784)) (Checked.append (checkChunk_sound 390912 128 c390912) (checkChunk_sound 391040 128 c391040))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 391168 128 c391168) (checkChunk_sound 391296 128 c391296)) (Checked.append (checkChunk_sound 391424 128 c391424) (checkChunk_sound 391552 128 c391552))) (Checked.append (Checked.append (checkChunk_sound 391680 128 c391680) (checkChunk_sound 391808 128 c391808)) (Checked.append (checkChunk_sound 391936 128 c391936) (checkChunk_sound 392064 128 c392064)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 392192 128 c392192) (checkChunk_sound 392320 128 c392320)) (Checked.append (checkChunk_sound 392448 128 c392448) (checkChunk_sound 392576 128 c392576))) (Checked.append (Checked.append (checkChunk_sound 392704 128 c392704) (checkChunk_sound 392832 128 c392832)) (Checked.append (checkChunk_sound 392960 128 c392960) (checkChunk_sound 393088 128 c393088)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01.B020
