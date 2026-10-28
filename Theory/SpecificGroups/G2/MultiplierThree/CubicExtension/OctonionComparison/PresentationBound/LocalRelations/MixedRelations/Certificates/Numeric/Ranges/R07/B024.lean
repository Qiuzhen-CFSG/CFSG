module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1695744, 1703936).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B024
private theorem c1695744 : checkChunk 1695744 128 = true := by decide +kernel
private theorem c1695872 : checkChunk 1695872 128 = true := by decide +kernel
private theorem c1696000 : checkChunk 1696000 128 = true := by decide +kernel
private theorem c1696128 : checkChunk 1696128 128 = true := by decide +kernel
private theorem c1696256 : checkChunk 1696256 128 = true := by decide +kernel
private theorem c1696384 : checkChunk 1696384 128 = true := by decide +kernel
private theorem c1696512 : checkChunk 1696512 128 = true := by decide +kernel
private theorem c1696640 : checkChunk 1696640 128 = true := by decide +kernel
private theorem c1696768 : checkChunk 1696768 128 = true := by decide +kernel
private theorem c1696896 : checkChunk 1696896 128 = true := by decide +kernel
private theorem c1697024 : checkChunk 1697024 128 = true := by decide +kernel
private theorem c1697152 : checkChunk 1697152 128 = true := by decide +kernel
private theorem c1697280 : checkChunk 1697280 128 = true := by decide +kernel
private theorem c1697408 : checkChunk 1697408 128 = true := by decide +kernel
private theorem c1697536 : checkChunk 1697536 128 = true := by decide +kernel
private theorem c1697664 : checkChunk 1697664 128 = true := by decide +kernel
private theorem c1697792 : checkChunk 1697792 128 = true := by decide +kernel
private theorem c1697920 : checkChunk 1697920 128 = true := by decide +kernel
private theorem c1698048 : checkChunk 1698048 128 = true := by decide +kernel
private theorem c1698176 : checkChunk 1698176 128 = true := by decide +kernel
private theorem c1698304 : checkChunk 1698304 128 = true := by decide +kernel
private theorem c1698432 : checkChunk 1698432 128 = true := by decide +kernel
private theorem c1698560 : checkChunk 1698560 128 = true := by decide +kernel
private theorem c1698688 : checkChunk 1698688 128 = true := by decide +kernel
private theorem c1698816 : checkChunk 1698816 128 = true := by decide +kernel
private theorem c1698944 : checkChunk 1698944 128 = true := by decide +kernel
private theorem c1699072 : checkChunk 1699072 128 = true := by decide +kernel
private theorem c1699200 : checkChunk 1699200 128 = true := by decide +kernel
private theorem c1699328 : checkChunk 1699328 128 = true := by decide +kernel
private theorem c1699456 : checkChunk 1699456 128 = true := by decide +kernel
private theorem c1699584 : checkChunk 1699584 128 = true := by decide +kernel
private theorem c1699712 : checkChunk 1699712 128 = true := by decide +kernel
private theorem c1699840 : checkChunk 1699840 128 = true := by decide +kernel
private theorem c1699968 : checkChunk 1699968 128 = true := by decide +kernel
private theorem c1700096 : checkChunk 1700096 128 = true := by decide +kernel
private theorem c1700224 : checkChunk 1700224 128 = true := by decide +kernel
private theorem c1700352 : checkChunk 1700352 128 = true := by decide +kernel
private theorem c1700480 : checkChunk 1700480 128 = true := by decide +kernel
private theorem c1700608 : checkChunk 1700608 128 = true := by decide +kernel
private theorem c1700736 : checkChunk 1700736 128 = true := by decide +kernel
private theorem c1700864 : checkChunk 1700864 128 = true := by decide +kernel
private theorem c1700992 : checkChunk 1700992 128 = true := by decide +kernel
private theorem c1701120 : checkChunk 1701120 128 = true := by decide +kernel
private theorem c1701248 : checkChunk 1701248 128 = true := by decide +kernel
private theorem c1701376 : checkChunk 1701376 128 = true := by decide +kernel
private theorem c1701504 : checkChunk 1701504 128 = true := by decide +kernel
private theorem c1701632 : checkChunk 1701632 128 = true := by decide +kernel
private theorem c1701760 : checkChunk 1701760 128 = true := by decide +kernel
private theorem c1701888 : checkChunk 1701888 128 = true := by decide +kernel
private theorem c1702016 : checkChunk 1702016 128 = true := by decide +kernel
private theorem c1702144 : checkChunk 1702144 128 = true := by decide +kernel
private theorem c1702272 : checkChunk 1702272 128 = true := by decide +kernel
private theorem c1702400 : checkChunk 1702400 128 = true := by decide +kernel
private theorem c1702528 : checkChunk 1702528 128 = true := by decide +kernel
private theorem c1702656 : checkChunk 1702656 128 = true := by decide +kernel
private theorem c1702784 : checkChunk 1702784 128 = true := by decide +kernel
private theorem c1702912 : checkChunk 1702912 128 = true := by decide +kernel
private theorem c1703040 : checkChunk 1703040 128 = true := by decide +kernel
private theorem c1703168 : checkChunk 1703168 128 = true := by decide +kernel
private theorem c1703296 : checkChunk 1703296 128 = true := by decide +kernel
private theorem c1703424 : checkChunk 1703424 128 = true := by decide +kernel
private theorem c1703552 : checkChunk 1703552 128 = true := by decide +kernel
private theorem c1703680 : checkChunk 1703680 128 = true := by decide +kernel
private theorem c1703808 : checkChunk 1703808 128 = true := by decide +kernel

public theorem checked : Checked 1695744 1703936 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1695744 128 c1695744) (checkChunk_sound 1695872 128 c1695872)) (Checked.append (checkChunk_sound 1696000 128 c1696000) (checkChunk_sound 1696128 128 c1696128))) (Checked.append (Checked.append (checkChunk_sound 1696256 128 c1696256) (checkChunk_sound 1696384 128 c1696384)) (Checked.append (checkChunk_sound 1696512 128 c1696512) (checkChunk_sound 1696640 128 c1696640)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1696768 128 c1696768) (checkChunk_sound 1696896 128 c1696896)) (Checked.append (checkChunk_sound 1697024 128 c1697024) (checkChunk_sound 1697152 128 c1697152))) (Checked.append (Checked.append (checkChunk_sound 1697280 128 c1697280) (checkChunk_sound 1697408 128 c1697408)) (Checked.append (checkChunk_sound 1697536 128 c1697536) (checkChunk_sound 1697664 128 c1697664))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1697792 128 c1697792) (checkChunk_sound 1697920 128 c1697920)) (Checked.append (checkChunk_sound 1698048 128 c1698048) (checkChunk_sound 1698176 128 c1698176))) (Checked.append (Checked.append (checkChunk_sound 1698304 128 c1698304) (checkChunk_sound 1698432 128 c1698432)) (Checked.append (checkChunk_sound 1698560 128 c1698560) (checkChunk_sound 1698688 128 c1698688)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1698816 128 c1698816) (checkChunk_sound 1698944 128 c1698944)) (Checked.append (checkChunk_sound 1699072 128 c1699072) (checkChunk_sound 1699200 128 c1699200))) (Checked.append (Checked.append (checkChunk_sound 1699328 128 c1699328) (checkChunk_sound 1699456 128 c1699456)) (Checked.append (checkChunk_sound 1699584 128 c1699584) (checkChunk_sound 1699712 128 c1699712)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1699840 128 c1699840) (checkChunk_sound 1699968 128 c1699968)) (Checked.append (checkChunk_sound 1700096 128 c1700096) (checkChunk_sound 1700224 128 c1700224))) (Checked.append (Checked.append (checkChunk_sound 1700352 128 c1700352) (checkChunk_sound 1700480 128 c1700480)) (Checked.append (checkChunk_sound 1700608 128 c1700608) (checkChunk_sound 1700736 128 c1700736)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1700864 128 c1700864) (checkChunk_sound 1700992 128 c1700992)) (Checked.append (checkChunk_sound 1701120 128 c1701120) (checkChunk_sound 1701248 128 c1701248))) (Checked.append (Checked.append (checkChunk_sound 1701376 128 c1701376) (checkChunk_sound 1701504 128 c1701504)) (Checked.append (checkChunk_sound 1701632 128 c1701632) (checkChunk_sound 1701760 128 c1701760))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1701888 128 c1701888) (checkChunk_sound 1702016 128 c1702016)) (Checked.append (checkChunk_sound 1702144 128 c1702144) (checkChunk_sound 1702272 128 c1702272))) (Checked.append (Checked.append (checkChunk_sound 1702400 128 c1702400) (checkChunk_sound 1702528 128 c1702528)) (Checked.append (checkChunk_sound 1702656 128 c1702656) (checkChunk_sound 1702784 128 c1702784)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1702912 128 c1702912) (checkChunk_sound 1703040 128 c1703040)) (Checked.append (checkChunk_sound 1703168 128 c1703168) (checkChunk_sound 1703296 128 c1703296))) (Checked.append (Checked.append (checkChunk_sound 1703424 128 c1703424) (checkChunk_sound 1703552 128 c1703552)) (Checked.append (checkChunk_sound 1703680 128 c1703680) (checkChunk_sound 1703808 128 c1703808)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B024
