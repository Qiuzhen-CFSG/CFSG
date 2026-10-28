module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [671744, 679936).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B003
private theorem c671744 : checkChunk 671744 128 = true := by decide +kernel
private theorem c671872 : checkChunk 671872 128 = true := by decide +kernel
private theorem c672000 : checkChunk 672000 128 = true := by decide +kernel
private theorem c672128 : checkChunk 672128 128 = true := by decide +kernel
private theorem c672256 : checkChunk 672256 128 = true := by decide +kernel
private theorem c672384 : checkChunk 672384 128 = true := by decide +kernel
private theorem c672512 : checkChunk 672512 128 = true := by decide +kernel
private theorem c672640 : checkChunk 672640 128 = true := by decide +kernel
private theorem c672768 : checkChunk 672768 128 = true := by decide +kernel
private theorem c672896 : checkChunk 672896 128 = true := by decide +kernel
private theorem c673024 : checkChunk 673024 128 = true := by decide +kernel
private theorem c673152 : checkChunk 673152 128 = true := by decide +kernel
private theorem c673280 : checkChunk 673280 128 = true := by decide +kernel
private theorem c673408 : checkChunk 673408 128 = true := by decide +kernel
private theorem c673536 : checkChunk 673536 128 = true := by decide +kernel
private theorem c673664 : checkChunk 673664 128 = true := by decide +kernel
private theorem c673792 : checkChunk 673792 128 = true := by decide +kernel
private theorem c673920 : checkChunk 673920 128 = true := by decide +kernel
private theorem c674048 : checkChunk 674048 128 = true := by decide +kernel
private theorem c674176 : checkChunk 674176 128 = true := by decide +kernel
private theorem c674304 : checkChunk 674304 128 = true := by decide +kernel
private theorem c674432 : checkChunk 674432 128 = true := by decide +kernel
private theorem c674560 : checkChunk 674560 128 = true := by decide +kernel
private theorem c674688 : checkChunk 674688 128 = true := by decide +kernel
private theorem c674816 : checkChunk 674816 128 = true := by decide +kernel
private theorem c674944 : checkChunk 674944 128 = true := by decide +kernel
private theorem c675072 : checkChunk 675072 128 = true := by decide +kernel
private theorem c675200 : checkChunk 675200 128 = true := by decide +kernel
private theorem c675328 : checkChunk 675328 128 = true := by decide +kernel
private theorem c675456 : checkChunk 675456 128 = true := by decide +kernel
private theorem c675584 : checkChunk 675584 128 = true := by decide +kernel
private theorem c675712 : checkChunk 675712 128 = true := by decide +kernel
private theorem c675840 : checkChunk 675840 128 = true := by decide +kernel
private theorem c675968 : checkChunk 675968 128 = true := by decide +kernel
private theorem c676096 : checkChunk 676096 128 = true := by decide +kernel
private theorem c676224 : checkChunk 676224 128 = true := by decide +kernel
private theorem c676352 : checkChunk 676352 128 = true := by decide +kernel
private theorem c676480 : checkChunk 676480 128 = true := by decide +kernel
private theorem c676608 : checkChunk 676608 128 = true := by decide +kernel
private theorem c676736 : checkChunk 676736 128 = true := by decide +kernel
private theorem c676864 : checkChunk 676864 128 = true := by decide +kernel
private theorem c676992 : checkChunk 676992 128 = true := by decide +kernel
private theorem c677120 : checkChunk 677120 128 = true := by decide +kernel
private theorem c677248 : checkChunk 677248 128 = true := by decide +kernel
private theorem c677376 : checkChunk 677376 128 = true := by decide +kernel
private theorem c677504 : checkChunk 677504 128 = true := by decide +kernel
private theorem c677632 : checkChunk 677632 128 = true := by decide +kernel
private theorem c677760 : checkChunk 677760 128 = true := by decide +kernel
private theorem c677888 : checkChunk 677888 128 = true := by decide +kernel
private theorem c678016 : checkChunk 678016 128 = true := by decide +kernel
private theorem c678144 : checkChunk 678144 128 = true := by decide +kernel
private theorem c678272 : checkChunk 678272 128 = true := by decide +kernel
private theorem c678400 : checkChunk 678400 128 = true := by decide +kernel
private theorem c678528 : checkChunk 678528 128 = true := by decide +kernel
private theorem c678656 : checkChunk 678656 128 = true := by decide +kernel
private theorem c678784 : checkChunk 678784 128 = true := by decide +kernel
private theorem c678912 : checkChunk 678912 128 = true := by decide +kernel
private theorem c679040 : checkChunk 679040 128 = true := by decide +kernel
private theorem c679168 : checkChunk 679168 128 = true := by decide +kernel
private theorem c679296 : checkChunk 679296 128 = true := by decide +kernel
private theorem c679424 : checkChunk 679424 128 = true := by decide +kernel
private theorem c679552 : checkChunk 679552 128 = true := by decide +kernel
private theorem c679680 : checkChunk 679680 128 = true := by decide +kernel
private theorem c679808 : checkChunk 679808 128 = true := by decide +kernel

public theorem checked : Checked 671744 679936 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 671744 128 c671744) (checkChunk_sound 671872 128 c671872)) (Checked.append (checkChunk_sound 672000 128 c672000) (checkChunk_sound 672128 128 c672128))) (Checked.append (Checked.append (checkChunk_sound 672256 128 c672256) (checkChunk_sound 672384 128 c672384)) (Checked.append (checkChunk_sound 672512 128 c672512) (checkChunk_sound 672640 128 c672640)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 672768 128 c672768) (checkChunk_sound 672896 128 c672896)) (Checked.append (checkChunk_sound 673024 128 c673024) (checkChunk_sound 673152 128 c673152))) (Checked.append (Checked.append (checkChunk_sound 673280 128 c673280) (checkChunk_sound 673408 128 c673408)) (Checked.append (checkChunk_sound 673536 128 c673536) (checkChunk_sound 673664 128 c673664))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 673792 128 c673792) (checkChunk_sound 673920 128 c673920)) (Checked.append (checkChunk_sound 674048 128 c674048) (checkChunk_sound 674176 128 c674176))) (Checked.append (Checked.append (checkChunk_sound 674304 128 c674304) (checkChunk_sound 674432 128 c674432)) (Checked.append (checkChunk_sound 674560 128 c674560) (checkChunk_sound 674688 128 c674688)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 674816 128 c674816) (checkChunk_sound 674944 128 c674944)) (Checked.append (checkChunk_sound 675072 128 c675072) (checkChunk_sound 675200 128 c675200))) (Checked.append (Checked.append (checkChunk_sound 675328 128 c675328) (checkChunk_sound 675456 128 c675456)) (Checked.append (checkChunk_sound 675584 128 c675584) (checkChunk_sound 675712 128 c675712)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 675840 128 c675840) (checkChunk_sound 675968 128 c675968)) (Checked.append (checkChunk_sound 676096 128 c676096) (checkChunk_sound 676224 128 c676224))) (Checked.append (Checked.append (checkChunk_sound 676352 128 c676352) (checkChunk_sound 676480 128 c676480)) (Checked.append (checkChunk_sound 676608 128 c676608) (checkChunk_sound 676736 128 c676736)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 676864 128 c676864) (checkChunk_sound 676992 128 c676992)) (Checked.append (checkChunk_sound 677120 128 c677120) (checkChunk_sound 677248 128 c677248))) (Checked.append (Checked.append (checkChunk_sound 677376 128 c677376) (checkChunk_sound 677504 128 c677504)) (Checked.append (checkChunk_sound 677632 128 c677632) (checkChunk_sound 677760 128 c677760))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 677888 128 c677888) (checkChunk_sound 678016 128 c678016)) (Checked.append (checkChunk_sound 678144 128 c678144) (checkChunk_sound 678272 128 c678272))) (Checked.append (Checked.append (checkChunk_sound 678400 128 c678400) (checkChunk_sound 678528 128 c678528)) (Checked.append (checkChunk_sound 678656 128 c678656) (checkChunk_sound 678784 128 c678784)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 678912 128 c678912) (checkChunk_sound 679040 128 c679040)) (Checked.append (checkChunk_sound 679168 128 c679168) (checkChunk_sound 679296 128 c679296))) (Checked.append (Checked.append (checkChunk_sound 679424 128 c679424) (checkChunk_sound 679552 128 c679552)) (Checked.append (checkChunk_sound 679680 128 c679680) (checkChunk_sound 679808 128 c679808)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03.B003
