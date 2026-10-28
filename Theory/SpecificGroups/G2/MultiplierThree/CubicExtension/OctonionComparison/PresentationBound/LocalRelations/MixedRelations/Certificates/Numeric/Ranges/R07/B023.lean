module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1687552, 1695744).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B023
private theorem c1687552 : checkChunk 1687552 128 = true := by decide +kernel
private theorem c1687680 : checkChunk 1687680 128 = true := by decide +kernel
private theorem c1687808 : checkChunk 1687808 128 = true := by decide +kernel
private theorem c1687936 : checkChunk 1687936 128 = true := by decide +kernel
private theorem c1688064 : checkChunk 1688064 128 = true := by decide +kernel
private theorem c1688192 : checkChunk 1688192 128 = true := by decide +kernel
private theorem c1688320 : checkChunk 1688320 128 = true := by decide +kernel
private theorem c1688448 : checkChunk 1688448 128 = true := by decide +kernel
private theorem c1688576 : checkChunk 1688576 128 = true := by decide +kernel
private theorem c1688704 : checkChunk 1688704 128 = true := by decide +kernel
private theorem c1688832 : checkChunk 1688832 128 = true := by decide +kernel
private theorem c1688960 : checkChunk 1688960 128 = true := by decide +kernel
private theorem c1689088 : checkChunk 1689088 128 = true := by decide +kernel
private theorem c1689216 : checkChunk 1689216 128 = true := by decide +kernel
private theorem c1689344 : checkChunk 1689344 128 = true := by decide +kernel
private theorem c1689472 : checkChunk 1689472 128 = true := by decide +kernel
private theorem c1689600 : checkChunk 1689600 128 = true := by decide +kernel
private theorem c1689728 : checkChunk 1689728 128 = true := by decide +kernel
private theorem c1689856 : checkChunk 1689856 128 = true := by decide +kernel
private theorem c1689984 : checkChunk 1689984 128 = true := by decide +kernel
private theorem c1690112 : checkChunk 1690112 128 = true := by decide +kernel
private theorem c1690240 : checkChunk 1690240 128 = true := by decide +kernel
private theorem c1690368 : checkChunk 1690368 128 = true := by decide +kernel
private theorem c1690496 : checkChunk 1690496 128 = true := by decide +kernel
private theorem c1690624 : checkChunk 1690624 128 = true := by decide +kernel
private theorem c1690752 : checkChunk 1690752 128 = true := by decide +kernel
private theorem c1690880 : checkChunk 1690880 128 = true := by decide +kernel
private theorem c1691008 : checkChunk 1691008 128 = true := by decide +kernel
private theorem c1691136 : checkChunk 1691136 128 = true := by decide +kernel
private theorem c1691264 : checkChunk 1691264 128 = true := by decide +kernel
private theorem c1691392 : checkChunk 1691392 128 = true := by decide +kernel
private theorem c1691520 : checkChunk 1691520 128 = true := by decide +kernel
private theorem c1691648 : checkChunk 1691648 128 = true := by decide +kernel
private theorem c1691776 : checkChunk 1691776 128 = true := by decide +kernel
private theorem c1691904 : checkChunk 1691904 128 = true := by decide +kernel
private theorem c1692032 : checkChunk 1692032 128 = true := by decide +kernel
private theorem c1692160 : checkChunk 1692160 128 = true := by decide +kernel
private theorem c1692288 : checkChunk 1692288 128 = true := by decide +kernel
private theorem c1692416 : checkChunk 1692416 128 = true := by decide +kernel
private theorem c1692544 : checkChunk 1692544 128 = true := by decide +kernel
private theorem c1692672 : checkChunk 1692672 128 = true := by decide +kernel
private theorem c1692800 : checkChunk 1692800 128 = true := by decide +kernel
private theorem c1692928 : checkChunk 1692928 128 = true := by decide +kernel
private theorem c1693056 : checkChunk 1693056 128 = true := by decide +kernel
private theorem c1693184 : checkChunk 1693184 128 = true := by decide +kernel
private theorem c1693312 : checkChunk 1693312 128 = true := by decide +kernel
private theorem c1693440 : checkChunk 1693440 128 = true := by decide +kernel
private theorem c1693568 : checkChunk 1693568 128 = true := by decide +kernel
private theorem c1693696 : checkChunk 1693696 128 = true := by decide +kernel
private theorem c1693824 : checkChunk 1693824 128 = true := by decide +kernel
private theorem c1693952 : checkChunk 1693952 128 = true := by decide +kernel
private theorem c1694080 : checkChunk 1694080 128 = true := by decide +kernel
private theorem c1694208 : checkChunk 1694208 128 = true := by decide +kernel
private theorem c1694336 : checkChunk 1694336 128 = true := by decide +kernel
private theorem c1694464 : checkChunk 1694464 128 = true := by decide +kernel
private theorem c1694592 : checkChunk 1694592 128 = true := by decide +kernel
private theorem c1694720 : checkChunk 1694720 128 = true := by decide +kernel
private theorem c1694848 : checkChunk 1694848 128 = true := by decide +kernel
private theorem c1694976 : checkChunk 1694976 128 = true := by decide +kernel
private theorem c1695104 : checkChunk 1695104 128 = true := by decide +kernel
private theorem c1695232 : checkChunk 1695232 128 = true := by decide +kernel
private theorem c1695360 : checkChunk 1695360 128 = true := by decide +kernel
private theorem c1695488 : checkChunk 1695488 128 = true := by decide +kernel
private theorem c1695616 : checkChunk 1695616 128 = true := by decide +kernel

public theorem checked : Checked 1687552 1695744 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1687552 128 c1687552) (checkChunk_sound 1687680 128 c1687680)) (Checked.append (checkChunk_sound 1687808 128 c1687808) (checkChunk_sound 1687936 128 c1687936))) (Checked.append (Checked.append (checkChunk_sound 1688064 128 c1688064) (checkChunk_sound 1688192 128 c1688192)) (Checked.append (checkChunk_sound 1688320 128 c1688320) (checkChunk_sound 1688448 128 c1688448)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1688576 128 c1688576) (checkChunk_sound 1688704 128 c1688704)) (Checked.append (checkChunk_sound 1688832 128 c1688832) (checkChunk_sound 1688960 128 c1688960))) (Checked.append (Checked.append (checkChunk_sound 1689088 128 c1689088) (checkChunk_sound 1689216 128 c1689216)) (Checked.append (checkChunk_sound 1689344 128 c1689344) (checkChunk_sound 1689472 128 c1689472))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1689600 128 c1689600) (checkChunk_sound 1689728 128 c1689728)) (Checked.append (checkChunk_sound 1689856 128 c1689856) (checkChunk_sound 1689984 128 c1689984))) (Checked.append (Checked.append (checkChunk_sound 1690112 128 c1690112) (checkChunk_sound 1690240 128 c1690240)) (Checked.append (checkChunk_sound 1690368 128 c1690368) (checkChunk_sound 1690496 128 c1690496)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1690624 128 c1690624) (checkChunk_sound 1690752 128 c1690752)) (Checked.append (checkChunk_sound 1690880 128 c1690880) (checkChunk_sound 1691008 128 c1691008))) (Checked.append (Checked.append (checkChunk_sound 1691136 128 c1691136) (checkChunk_sound 1691264 128 c1691264)) (Checked.append (checkChunk_sound 1691392 128 c1691392) (checkChunk_sound 1691520 128 c1691520)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1691648 128 c1691648) (checkChunk_sound 1691776 128 c1691776)) (Checked.append (checkChunk_sound 1691904 128 c1691904) (checkChunk_sound 1692032 128 c1692032))) (Checked.append (Checked.append (checkChunk_sound 1692160 128 c1692160) (checkChunk_sound 1692288 128 c1692288)) (Checked.append (checkChunk_sound 1692416 128 c1692416) (checkChunk_sound 1692544 128 c1692544)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1692672 128 c1692672) (checkChunk_sound 1692800 128 c1692800)) (Checked.append (checkChunk_sound 1692928 128 c1692928) (checkChunk_sound 1693056 128 c1693056))) (Checked.append (Checked.append (checkChunk_sound 1693184 128 c1693184) (checkChunk_sound 1693312 128 c1693312)) (Checked.append (checkChunk_sound 1693440 128 c1693440) (checkChunk_sound 1693568 128 c1693568))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1693696 128 c1693696) (checkChunk_sound 1693824 128 c1693824)) (Checked.append (checkChunk_sound 1693952 128 c1693952) (checkChunk_sound 1694080 128 c1694080))) (Checked.append (Checked.append (checkChunk_sound 1694208 128 c1694208) (checkChunk_sound 1694336 128 c1694336)) (Checked.append (checkChunk_sound 1694464 128 c1694464) (checkChunk_sound 1694592 128 c1694592)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1694720 128 c1694720) (checkChunk_sound 1694848 128 c1694848)) (Checked.append (checkChunk_sound 1694976 128 c1694976) (checkChunk_sound 1695104 128 c1695104))) (Checked.append (Checked.append (checkChunk_sound 1695232 128 c1695232) (checkChunk_sound 1695360 128 c1695360)) (Checked.append (checkChunk_sound 1695488 128 c1695488) (checkChunk_sound 1695616 128 c1695616)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07.B023
