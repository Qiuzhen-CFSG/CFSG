module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Chunks
/-! Kernel checks for retained cyclic trace instructions [1433600, 1441792).
Source: the pinned ATLAS G23G1-P1 trace; see ../../../source/README.md. -/
set_option Elab.async false
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B018
private theorem c1433600 : checkChunk 1433600 128 = true := by decide +kernel
private theorem c1433728 : checkChunk 1433728 128 = true := by decide +kernel
private theorem c1433856 : checkChunk 1433856 128 = true := by decide +kernel
private theorem c1433984 : checkChunk 1433984 128 = true := by decide +kernel
private theorem c1434112 : checkChunk 1434112 128 = true := by decide +kernel
private theorem c1434240 : checkChunk 1434240 128 = true := by decide +kernel
private theorem c1434368 : checkChunk 1434368 128 = true := by decide +kernel
private theorem c1434496 : checkChunk 1434496 128 = true := by decide +kernel
private theorem c1434624 : checkChunk 1434624 128 = true := by decide +kernel
private theorem c1434752 : checkChunk 1434752 128 = true := by decide +kernel
private theorem c1434880 : checkChunk 1434880 128 = true := by decide +kernel
private theorem c1435008 : checkChunk 1435008 128 = true := by decide +kernel
private theorem c1435136 : checkChunk 1435136 128 = true := by decide +kernel
private theorem c1435264 : checkChunk 1435264 128 = true := by decide +kernel
private theorem c1435392 : checkChunk 1435392 128 = true := by decide +kernel
private theorem c1435520 : checkChunk 1435520 128 = true := by decide +kernel
private theorem c1435648 : checkChunk 1435648 128 = true := by decide +kernel
private theorem c1435776 : checkChunk 1435776 128 = true := by decide +kernel
private theorem c1435904 : checkChunk 1435904 128 = true := by decide +kernel
private theorem c1436032 : checkChunk 1436032 128 = true := by decide +kernel
private theorem c1436160 : checkChunk 1436160 128 = true := by decide +kernel
private theorem c1436288 : checkChunk 1436288 128 = true := by decide +kernel
private theorem c1436416 : checkChunk 1436416 128 = true := by decide +kernel
private theorem c1436544 : checkChunk 1436544 128 = true := by decide +kernel
private theorem c1436672 : checkChunk 1436672 128 = true := by decide +kernel
private theorem c1436800 : checkChunk 1436800 128 = true := by decide +kernel
private theorem c1436928 : checkChunk 1436928 128 = true := by decide +kernel
private theorem c1437056 : checkChunk 1437056 128 = true := by decide +kernel
private theorem c1437184 : checkChunk 1437184 128 = true := by decide +kernel
private theorem c1437312 : checkChunk 1437312 128 = true := by decide +kernel
private theorem c1437440 : checkChunk 1437440 128 = true := by decide +kernel
private theorem c1437568 : checkChunk 1437568 128 = true := by decide +kernel
private theorem c1437696 : checkChunk 1437696 128 = true := by decide +kernel
private theorem c1437824 : checkChunk 1437824 128 = true := by decide +kernel
private theorem c1437952 : checkChunk 1437952 128 = true := by decide +kernel
private theorem c1438080 : checkChunk 1438080 128 = true := by decide +kernel
private theorem c1438208 : checkChunk 1438208 128 = true := by decide +kernel
private theorem c1438336 : checkChunk 1438336 128 = true := by decide +kernel
private theorem c1438464 : checkChunk 1438464 128 = true := by decide +kernel
private theorem c1438592 : checkChunk 1438592 128 = true := by decide +kernel
private theorem c1438720 : checkChunk 1438720 128 = true := by decide +kernel
private theorem c1438848 : checkChunk 1438848 128 = true := by decide +kernel
private theorem c1438976 : checkChunk 1438976 128 = true := by decide +kernel
private theorem c1439104 : checkChunk 1439104 128 = true := by decide +kernel
private theorem c1439232 : checkChunk 1439232 128 = true := by decide +kernel
private theorem c1439360 : checkChunk 1439360 128 = true := by decide +kernel
private theorem c1439488 : checkChunk 1439488 128 = true := by decide +kernel
private theorem c1439616 : checkChunk 1439616 128 = true := by decide +kernel
private theorem c1439744 : checkChunk 1439744 128 = true := by decide +kernel
private theorem c1439872 : checkChunk 1439872 128 = true := by decide +kernel
private theorem c1440000 : checkChunk 1440000 128 = true := by decide +kernel
private theorem c1440128 : checkChunk 1440128 128 = true := by decide +kernel
private theorem c1440256 : checkChunk 1440256 128 = true := by decide +kernel
private theorem c1440384 : checkChunk 1440384 128 = true := by decide +kernel
private theorem c1440512 : checkChunk 1440512 128 = true := by decide +kernel
private theorem c1440640 : checkChunk 1440640 128 = true := by decide +kernel
private theorem c1440768 : checkChunk 1440768 128 = true := by decide +kernel
private theorem c1440896 : checkChunk 1440896 128 = true := by decide +kernel
private theorem c1441024 : checkChunk 1441024 128 = true := by decide +kernel
private theorem c1441152 : checkChunk 1441152 128 = true := by decide +kernel
private theorem c1441280 : checkChunk 1441280 128 = true := by decide +kernel
private theorem c1441408 : checkChunk 1441408 128 = true := by decide +kernel
private theorem c1441536 : checkChunk 1441536 128 = true := by decide +kernel
private theorem c1441664 : checkChunk 1441664 128 = true := by decide +kernel

public theorem checked : Checked 1433600 1441792 :=
  (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1433600 128 c1433600) (checkChunk_sound 1433728 128 c1433728)) (Checked.append (checkChunk_sound 1433856 128 c1433856) (checkChunk_sound 1433984 128 c1433984))) (Checked.append (Checked.append (checkChunk_sound 1434112 128 c1434112) (checkChunk_sound 1434240 128 c1434240)) (Checked.append (checkChunk_sound 1434368 128 c1434368) (checkChunk_sound 1434496 128 c1434496)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1434624 128 c1434624) (checkChunk_sound 1434752 128 c1434752)) (Checked.append (checkChunk_sound 1434880 128 c1434880) (checkChunk_sound 1435008 128 c1435008))) (Checked.append (Checked.append (checkChunk_sound 1435136 128 c1435136) (checkChunk_sound 1435264 128 c1435264)) (Checked.append (checkChunk_sound 1435392 128 c1435392) (checkChunk_sound 1435520 128 c1435520))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1435648 128 c1435648) (checkChunk_sound 1435776 128 c1435776)) (Checked.append (checkChunk_sound 1435904 128 c1435904) (checkChunk_sound 1436032 128 c1436032))) (Checked.append (Checked.append (checkChunk_sound 1436160 128 c1436160) (checkChunk_sound 1436288 128 c1436288)) (Checked.append (checkChunk_sound 1436416 128 c1436416) (checkChunk_sound 1436544 128 c1436544)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1436672 128 c1436672) (checkChunk_sound 1436800 128 c1436800)) (Checked.append (checkChunk_sound 1436928 128 c1436928) (checkChunk_sound 1437056 128 c1437056))) (Checked.append (Checked.append (checkChunk_sound 1437184 128 c1437184) (checkChunk_sound 1437312 128 c1437312)) (Checked.append (checkChunk_sound 1437440 128 c1437440) (checkChunk_sound 1437568 128 c1437568)))))) (Checked.append (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1437696 128 c1437696) (checkChunk_sound 1437824 128 c1437824)) (Checked.append (checkChunk_sound 1437952 128 c1437952) (checkChunk_sound 1438080 128 c1438080))) (Checked.append (Checked.append (checkChunk_sound 1438208 128 c1438208) (checkChunk_sound 1438336 128 c1438336)) (Checked.append (checkChunk_sound 1438464 128 c1438464) (checkChunk_sound 1438592 128 c1438592)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1438720 128 c1438720) (checkChunk_sound 1438848 128 c1438848)) (Checked.append (checkChunk_sound 1438976 128 c1438976) (checkChunk_sound 1439104 128 c1439104))) (Checked.append (Checked.append (checkChunk_sound 1439232 128 c1439232) (checkChunk_sound 1439360 128 c1439360)) (Checked.append (checkChunk_sound 1439488 128 c1439488) (checkChunk_sound 1439616 128 c1439616))))) (Checked.append (Checked.append (Checked.append (Checked.append (checkChunk_sound 1439744 128 c1439744) (checkChunk_sound 1439872 128 c1439872)) (Checked.append (checkChunk_sound 1440000 128 c1440000) (checkChunk_sound 1440128 128 c1440128))) (Checked.append (Checked.append (checkChunk_sound 1440256 128 c1440256) (checkChunk_sound 1440384 128 c1440384)) (Checked.append (checkChunk_sound 1440512 128 c1440512) (checkChunk_sound 1440640 128 c1440640)))) (Checked.append (Checked.append (Checked.append (checkChunk_sound 1440768 128 c1440768) (checkChunk_sound 1440896 128 c1440896)) (Checked.append (checkChunk_sound 1441024 128 c1441024) (checkChunk_sound 1441152 128 c1441152))) (Checked.append (Checked.append (checkChunk_sound 1441280 128 c1441280) (checkChunk_sound 1441408 128 c1441408)) (Checked.append (checkChunk_sound 1441536 128 c1441536) (checkChunk_sound 1441664 128 c1441664)))))))
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06.B018
